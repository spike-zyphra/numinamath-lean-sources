import Mathlib

theorem algebra_2903 {S : Finset ℝ} (hS : ∀ x, x ∈ S ↔ (3 - x) = 0 ∨ (|x - 1| - 2) = 0) :
    ∑ x in S, x = 2 := by
  have h1 : S = { -1, 3 } := by
    ext x
    simp [hS]
    constructor
    · -- Assume x ∈ S, prove x ∈ { -1, 3 }
      intro h
      rcases h with (h1 | h1)
      · -- Case where (3 - x) = 0, so x = 3
        right
        linarith
      · -- Case where |x - 1| - 2 = 0, so |x - 1| = 2
        have h_eq : |x - 1| = 2 := by linarith
        cases eq_or_eq_neg_of_abs_eq h_eq with
        | inl h2 =>
          right
          linarith
        | inr h2 =>
          left
          linarith
    · -- Assume x ∈ { -1, 3 }, prove x ∈ S
      rintro (h | h)
      · -- Case x = -1
        rw [h]
        norm_num
      · -- Case x = 3
        rw [h]
        norm_num
  rw [h1]
  norm_num [Finset.sum_insert, Finset.sum_singleton]