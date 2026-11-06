import Mathlib

open Finset Function

/-
Problem:
We need to determine the number of distinct paths a bug can take from the vertex (0,0,0,0) to (1,1,1,1) in a 4-dimensional hypercube (H) by moving exactly 4 steps along the edges of H. Each step must increment exactly one coordinate from 0 to 1, and once a coordinate is incremented, it cannot be changed again.
-/
theorem Combinatorics_609387 :
    Nat.card { path : Fin 4 → Fin 4 | 
    ∀ i j, i ≠ j → path i ≠ path j ∧
    ∀ k, ∃ i, path i = k } = 24 := by 

  -- Rewrite the cardinality of the set as the cardinality of a fintype
  rw [Nat.card_eq_fintype_card]
  
  -- Simplify set membership and coercion operations
  simp only [Set.coe_setOf, Set.mem_setOf_eq, Fintype.card_coe]

  -- Apply the formula for the cardinality of a subtype
  rw [Fintype.card_subtype]

  -- Simplify further using typeclass resolution and decidable instances
  simp
  
  -- Use native decision procedure to verify the result
  native_decide