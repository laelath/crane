# STM notes and TODOs

## Switch from universe pattern to axiomitized defs

Currently things are written with a universe pattern in order to have a computable implementation of TVar reads/writes.
This change from the initial interface is being reverted in favor of a propositional interpretation of TVar reads and writes, the new files can be found in `*Axiom.v`.
Switching back to axiomitied TVars is mainly being done for encapsulation purposes, as having them as axioms prevents any uses from inspecting the way that they are constructed making them truly opaque.

`WriteLogAxiom.v` needs to be updated to store the corresponding natural number for the TVar to get computational equality.
Alternatively the use of write logs can be dropped in favor of giving semantics for a global transaction store with unique transaction IDs that can either be committed or aborted. The start of this method can be found in `AtomicTransactionsAxiom.v`.
