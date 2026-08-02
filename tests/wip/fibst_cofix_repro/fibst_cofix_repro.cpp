#include "fibst_cofix_repro.h"

List<uint64_t> ListDef::seq(uint64_t start, uint64_t len) {
  std::shared_ptr<List<uint64_t>> _head{};
  std::shared_ptr<List<uint64_t>> *_write = &_head;
  uint64_t _loop_len = std::move(len);
  uint64_t _loop_start = std::move(start);
  while (true) {
    if (_loop_len <= 0) {
      *_write = std::make_shared<List<uint64_t>>(List<uint64_t>::nil());
      break;
    } else {
      uint64_t len0 = _loop_len - 1;
      auto _cell = std::make_shared<List<uint64_t>>(
          typename List<uint64_t>::Cons(_loop_start, nullptr));
      *_write = std::move(_cell);
      _write = &std::get<typename List<uint64_t>::Cons>((*_write)->v_mut()).l;
      _loop_len = len0;
      _loop_start = (_loop_start + 1);
      continue;
    }
  }
  return std::move(*_head);
}
