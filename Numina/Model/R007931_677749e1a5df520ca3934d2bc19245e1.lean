import Mathlib

theorem algebra_10692 : ∏ᶠ x ∈ {x : ℝ | |x - 7| - 3 = -2}, x = 48 := by
  have h1 : {x : ℝ | |x - 7| - 3 = -2} = {6, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume |x - 7| - 3 = -2, prove x = 6 or x = 8
      intro h
      have h2 : |x - 7| = 1 := by linarith
      cases eq_or_eq_neg_of_abs_eq h2 with
      | inl h3 =>
        right
        linarith
      | inr h4 =>
        left
        linarith
    · -- Assume x = 6 or x = 8, prove |x - 7| - 3 = -2
      rintro (h | h)
      · -- Case x = 6
        rw [h]
        norm_num
      · -- Case x = 8
        rw [h]
        norm_num
  rw [h1]
  rw [finprod_mem_pair]
  all_goals norm_num