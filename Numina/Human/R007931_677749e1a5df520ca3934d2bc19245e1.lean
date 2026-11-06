import Mathlib

theorem algebra_10692 : ∏ᶠ x ∈ {x : ℝ | |x - 7| - 3 = -2}, x = 48 := by
  have h1 : {x : ℝ | |x - 7| - 3 = -2} = {6, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h2 : |x - 7| = 1 := by linarith
      cases eq_or_eq_neg_of_abs_eq h2 with
      | inl h3 =>
        right
        linarith
      | inr h4 =>
        left
        linarith
    · intro h
      cases h with
      | inl h1 =>
        rw [h1]
        norm_num
      | inr h2 =>
        rw [h2]
        norm_num
  rw [h1]
  rw [finprod_mem_pair (by norm_num)]
  norm_num