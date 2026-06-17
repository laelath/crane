#ifndef INCLUDED_STM
#define INCLUDED_STM

#include <memory>
#include <stm_adapter.h>
#include <system_error>
#include <type_traits>
#include <utility>
#include <variant>
#include <vector>

template <typename A> struct List {
  // TYPES
  struct Nil {};

  struct Cons {
    A a;
    std::shared_ptr<List<A>> l;
  };

  using variant_t = std::variant<Nil, Cons>;

private:
  // DATA
  variant_t v_;

public:
  // CREATORS
  List() {}

  explicit List(Nil _v) : v_(_v) {}

  explicit List(Cons _v) : v_(std::move(_v)) {}

  template <typename _U> List(const List<_U> &_other) {
    if (std::holds_alternative<typename List<_U>::Nil>(_other.v())) {
      this->v_ = Nil{};
    } else {
      const auto &[a, l] = std::get<typename List<_U>::Cons>(_other.v());
      this->v_ = Cons{
          [&]() -> A {
            if constexpr (std::is_same_v<_U, std::any>) {
              if (a.type() == typeid(A))
                return std::any_cast<A>(a);
              if constexpr (requires {
                              typename A::first_type;
                              typename A::second_type;
                            }) {
                const auto &[_k, _v] =
                    std::any_cast<std::pair<std::any, std::any>>(a);
                return A{[&]() -> typename A::first_type {
                           if constexpr (std::is_same_v<typename A::first_type,
                                                        std::any>)
                             return _k;
                           else
                             return std::any_cast<typename A::first_type>(_k);
                         }(),
                         [&]() -> typename A::second_type {
                           if constexpr (std::is_same_v<typename A::second_type,
                                                        std::any>)
                             return _v;
                           else
                             return std::any_cast<typename A::second_type>(_v);
                         }()};
              }
              return std::any_cast<A>(a);
            } else
              return A(a);
          }(),
          l ? std::make_shared<List<A>>(*l) : nullptr};
    }
  }

  static List<A> nil() { return List(Nil{}); }

  static List<A> cons(A a, List<A> l) {
    return List(Cons{std::move(a), std::make_shared<List<A>>(std::move(l))});
  }

  // MANIPULATORS
  ~List() {
    std::vector<std::shared_ptr<List<A>>> _stack = {};
    auto _drain = [&](variant_t &_v) {
      if (auto *_alt = std::get_if<Cons>(&_v)) {
        if (_alt->l) {
          _stack.push_back(std::move(_alt->l));
        }
      }
    };
    _drain(v_mut());
    while (!_stack.empty()) {
      auto _cur = std::move(_stack.back());
      _stack.pop_back();
      if (_cur.use_count() == 1) {
        _drain(_cur->v_mut());
      }
    }
  }

  inline variant_t &v_mut() { return v_; }

  // ACCESSORS
  const variant_t &v() const { return v_; }

  List<A> app(List<A> m) const {
    if (std::holds_alternative<typename List<A>::Nil>(this->v())) {
      return m;
    } else {
      const auto &[a0, a1] = std::get<typename List<A>::Cons>(this->v());
      return List<A>::cons(a0, a1->app(std::move(m)));
    }
  }
};

struct STMDefs {
  template <typename T1 = void, typename T2 = void, typename T3, typename F1>
    requires std::is_invocable_r_v<T3, F1 &, T3 &>
  static void modifyTVar(const stm::TVar<T3> &a, F1 &&f);
};

struct stmtest {
  static uint64_t basic_read(uint64_t x);
  static uint64_t basic_write(uint64_t x);
  static uint64_t increment(uint64_t x);
  static uint64_t write_read(uint64_t x);

  template <typename T1 = void, typename T2 = void>
  static void stm_enqueue(const stm::TVar<List<uint64_t>> &q, uint64_t x) {
    List<uint64_t> xs = stm::readTVar(q);
    stm::writeTVar(
        q, std::move(xs).app(List<uint64_t>::cons(x, List<uint64_t>::nil())));
    return;
  }

  template <typename T1 = void, typename T2 = void>
  static uint64_t stm_dequeue(const stm::TVar<List<uint64_t>> &q) {
    List<uint64_t> xs = stm::readTVar(q);
    if (std::holds_alternative<typename List<uint64_t>::Nil>(xs.v_mut())) {
      return stm::retry<uint64_t>();
    } else {
      auto &[a0, a1] = std::get<typename List<uint64_t>::Cons>(xs.v_mut());
      stm::writeTVar(q, *a1);
      return a0;
    }
  }

  static uint64_t io_queue_roundtrip(uint64_t x, uint64_t y);
};

template <typename T1 = void, typename T2 = void, typename T3, typename F1>
  requires std::is_invocable_r_v<T3, F1 &, T3 &>
void STMDefs::modifyTVar(const stm::TVar<T3> &a, F1 &&f) {
  T3 val = stm::readTVar(a);
  stm::writeTVar(a, f(val));
  return;
}

#endif // INCLUDED_STM
