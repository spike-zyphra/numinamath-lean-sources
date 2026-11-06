import Mathlib

theorem algebra_10229 : Set.ncard {(x : ℝ) | |x - 7| = |x + 1|} = 1 := by
  have h1 : {(x : ℝ) | |x - 7| = |x + 1|} = {3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · -- Assume |x - 7| = |x + 1| prove x = 3
      intro h
      have h2 : x - 7 = x + 1 ∨ x - 7 = -(x + 1) := by
        cases' abs_eq_abs.1 h with h3 h4
        · -- Case where x - 7 = x + 1
          left
          linarith 
        · -- Case where x - 7 = -(x + 1)
          right
          linarith 
      cases h2 with
      | inl h3 =>
        -- Case where x - 7 = x + 1, which simplifies to -7 = 1, a contradiction
        exfalso
        linarith 
      | inr h4 =>
        -- Case where x - 7 = -(x + 1)
        -- solving x - 7 = -x - 1 
        linarith 
    · -- Assume x = 3 prove |x - 7| = |x + 1|
      intro h
      rw [h]
      norm_num 
  rw [h1]
  norm_num