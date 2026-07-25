#include <parser_frame_modtype_nil.h>
#include <iostream>

// Instantiating TheParser::parse forces the template body to compile.
// This is a COMPILE-TIME bug repro: the build FAILING here with
//
//   no viable conversion from
//     'pair<frame, deque<any>>' to 'pair<frame, deque<frame>>'
//
// IS the successful reproduction. It mirrors the real Parser.h:2620 failure
//   ('pair<Parser_frame, deque<any>>' -> 'pair<Parser_frame, deque<Parser_frame>>')
// where parse()'s let-bound `auto sk0` erases the list-parser_frame nil to
// std::deque<std::any>{} instead of std::deque<Parser_frame>{}.
int main() {
  auto n = TheParser::parse(Concrete_symbol::SA);
  std::cout << n << std::endl;
  return 0;
}
