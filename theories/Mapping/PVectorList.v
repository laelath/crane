(* Copyright 2026 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(** Opt-in extraction mapping: Coq [list] -> C++ [immer::flex_vector], with
    COMPLETENESS-AWARE ELEMENT WRAPPING (see [Boxed Element] in
    [g_extraction.mlg] / [WRAP.md]).

    Import this module to extract Coq lists as a persistent, cache-friendly
    [immer::flex_vector<T>] instead of the default [Datatypes::List<T>]
    shared_ptr-linked cons-list. immer's structural sharing gives O(log N)
    persistent update/concat while keeping value semantics.

    immer containers require a *complete* element type, but Coq lists are
    often recursive. The [Boxed Element "immer::box<%t0>"] clause tells Crane
    to wrap the element in [immer::box] *only at recursive occurrences*
    (element types that recurse through the list, e.g. a JSON AST node).
    Flat elements -- [char], [bool], pairs of flat types -- stay UNBOXED.

    - [%elem]  in the type/nil templates = the (possibly boxed) element slot;
      Crane fills it with [immer::box<T>] when [T] is recursive, else [T].
    - [%t0]/[%aN] in the match/cons templates stay bare; immer::box's implicit
      conversions (ctor from T, operator const T&) make cons/match work for
      both boxed and unboxed element representations.

    Requires immer headers on the include path (e.g. -I path/to/immer). *)
From Crane Require Extraction.
From Stdlib Require Import List.
From Stdlib Require Import String.
From Stdlib Require Import Ascii.

(** Map the [list] inductive type to [immer::flex_vector], boxing only
    recursive element occurrences. *)
Crane Extract Inductive list =>
  "immer::flex_vector<%elem>"
  [ "immer::flex_vector<%elem>{}"
    "%a1.push_front(%a0)" ]
  "if (%scrut.empty()) { %br0 } else { const %t0& %b1a0 = %scrut.front(); auto %b1a1 = %scrut.drop(1); %br1 }"
  Boxed Element "immer::box<%t0>"
  From "immer/flex_vector.hpp" "immer/box.hpp".

(** Core list functions that are element-representation-agnostic. *)
Crane Extract Inlined Constant Datatypes.length =>
  "static_cast<uint64_t>(%a0.size())" From "cstdint".

(* flex_vector concatenation is O(log N) structural and works for both boxed
   and unboxed element reps (both sides are the same flex_vector<%elem>). *)
Crane Extract Inlined Constant Datatypes.app =>
  "(%a0 + %a1)" From "immer/flex_vector.hpp".

(** String <-> list conversions. [list ascii] = [char] elements, which are
    never recursive, hence always UNBOXED [flex_vector<char>]. *)
Crane Extract Inlined Constant String.list_ascii_of_string =>
  "[&]() { const auto& _s = %a0; return immer::flex_vector<char>(_s.begin(), _s.end()); }()" From "immer/flex_vector.hpp".

Crane Extract Inlined Constant String.string_of_list_ascii =>
  "[&]() { std::string _r; for (const auto& _c : %a0) _r.push_back(_c); return _r; }()" From "string".

(* Higher-order list functions (map/rev/filter/fold_*/forallb/…) are
   intentionally NOT mapped: Crane extracts their Coq definitions recursively
   using the inductive nil/cons/match templates above, which already
   box-or-not per element type consistently. This keeps boxing logic in one
   place. *)
