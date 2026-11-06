import Mathlib

theorem algebra_21505 : ∏ᶠ x ∈ {(x : ℝ) | abs (x - 4) - 10 = 2}, x = -128 := by
  have h1 : {(x : ℝ) | abs (x - 4) - 10 = 2} = {16, -8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward implication: If x is a solution, then x ∈ {16, -8}
      intro h
      have h2 : abs (x - 4) = 12 := by linarith
      cases eq_or_eq_neg_of_abs_eq h2 with
      | inl h3 =>
        left
        linarith
      | inr h4 =>
        right
        linarith
    · -- Backward implication: If x ∈ {16, -8}, then x is a solution
      rintro (h | h)
      · -- Case x = 16
        rw [h]
        norm_num [abs_of_nonneg]
      · -- Case x = -8
        rw [h]
        norm_num [abs_of_nonneg]
  rw [h1]
  rw [finprod_mem_pair]
  norm_num
  all_goals norm_num