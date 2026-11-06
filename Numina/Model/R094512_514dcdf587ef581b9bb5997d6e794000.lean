import Mathlib

theorem algebra_218616 (x : ℝ) (hx : |x| ≠ 0) :
    (|x| ^ 2 + |x| - 6 = 0) ↔ (x = -2 ∨ x = 2) := by
  constructor
  · -- Forward direction: Assume |x|^2 + |x| - 6 = 0, prove x = -2 ∨ x = 2
    intro h
    have h1 : |x| ^ 2 + |x| - 6 = 0 := h
    have h2 : (|x| - 2) * (|x| + 3) = 0 := by 
      nlinarith
    cases' (mul_eq_zero.mp h2) with h3 h4
    · -- Case where |x| - 2 = 0, so |x| = 2
      have h5 : |x| = 2 := by linarith
      cases eq_or_eq_neg_of_abs_eq h5 with
      | inl h6 =>
        right
        exact h6
      | inr h7 =>
        left
        linarith
    · -- Case where |x| + 3 = 0, so |x| = -3
      have h5 : |x| = -3 := by linarith
      have h6 : |x| ≥ 0 := abs_nonneg x
      linarith
  · -- Backward direction: Assume x = -2 ∨ x = 2, prove |x| ^ 2 + |x| - 6 = 0
    rintro (h | h)
    · -- Case where x = -2
      rw [h]
      norm_num
    · -- Case where x = 2
      rw [h]
      norm_num