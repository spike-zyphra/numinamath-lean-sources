import Mathlib

theorem algebra_3724 : ∑ᶠ (x : ℝ) (_ : abs (2 * x - 1) = 7), x = 1 := by

  have h1 : {x : ℝ | abs (2 * x - 1) = 7} = {4, -3} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume abs (2 * x - 1) = 7, prove x ∈ {4, -3}
      intro h
      cases eq_or_eq_neg_of_abs_eq h with
      | inl h_eq =>
        left
        linarith
      | inr h_eq =>
        right
        linarith
    · -- Assume x ∈ {4, -3}, prove abs (2 * x - 1) = 7
      rintro (h | h)
      · -- Case x = 4
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]
      · -- Case x = -3
        rw [h]
        norm_num [abs_of_nonneg, abs_of_nonpos]

  rw [show ∑ᶠ (x : ℝ) (_ : abs (2 * x - 1) = 7), x = ∑ᶠ x ∈ {x : ℝ | abs (2 * x - 1) = 7}, x by
    congr
  ]
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num