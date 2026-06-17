#include "stm.h"

uint64_t stmtest::basic_read(uint64_t x) {
  stm::TVar<uint64_t> c = stm::atomically([&] { return stm::newTVar(x); });
  return stm::atomically([&] { return stm::readTVar(c); });
}

uint64_t stmtest::basic_write(uint64_t x) {
  stm::TVar<uint64_t> c =
      stm::atomically([&] { return stm::newTVar(UINT64_C(0)); });
  stm::atomically([&] {
    return [&]() {
      stm::writeTVar(c, x);
      return std::monostate{};
    }();
  });
  return stm::atomically([&] { return stm::readTVar(c); });
}

uint64_t stmtest::increment(uint64_t x) {
  stm::TVar<uint64_t> c = stm::atomically([&] { return stm::newTVar(x); });
  stm::atomically([&] {
    return [&]() {
      STMDefs::modifyTVar(c, [](uint64_t x0) { return (x0 + 1); });
      return std::monostate{};
    }();
  });
  return stm::atomically([&] { return stm::readTVar(c); });
}

uint64_t stmtest::write_read(uint64_t x) {
  stm::TVar<uint64_t> c =
      stm::atomically([&] { return stm::newTVar(UINT64_C(0)); });
  return stm::atomically([&] {
    return [=]() mutable {
      stm::writeTVar(c, x);
      return stm::readTVar(c);
    }();
  });
}

uint64_t stmtest::io_queue_roundtrip(uint64_t x, uint64_t y) {
  stm::TVar<List<uint64_t>> q =
      stm::atomically([&] { return stm::newTVar(List<uint64_t>::nil()); });
  stm::atomically([&] {
    return [&]() {
      stm_enqueue(q, x);
      stm_enqueue(q, y);
      return std::monostate{};
    }();
  });
  return stm::atomically([&] { return stm_dequeue(q); });
}
