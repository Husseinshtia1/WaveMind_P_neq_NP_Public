// SAT definition
Definition SAT := fun f => exists a, satisfies f a = true.
Axiom SAT_in_NP : In_NP SAT.