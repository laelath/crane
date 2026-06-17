(* Copyright 2025 Bloomberg Finance L.P. *)
(* Distributed under the terms of the GNU LGPL v2.1 license. *)
(**
   STM (Software Transactional Memory) effect events for the BDE flavor.

   Re-exports shared definitions from [STMDefs.v] and adds C++ extraction
   mappings targeting BDE.
*)
From Crane Require Extraction.
From Crane Require Import Mapping.BDE Monads.IOBDE External.VectorBDE.
From Crane Require Export Monads.STMDefs.

Crane Extract Inductive tvarE => ""
  [ "stm::newTVar(%a1)" "stm::readTVar(%a0)" "stm::writeTVar(%a0, %a1)" ]
  From "stm_adapter.h".

Crane Extract Inductive TVar => "stm::TVar<%t2>"
  [ "static_assert(false, ""mk_tvar should not be extracted, use NewTVar instead."")" ]
  From "stm_adapter.h".

Crane Extract Inlined Constant readTVar => "stm::readTVar(%a0)".
Crane Extract Inlined Constant writeTVar => "stm::writeTVar(%a0, %a1)".
