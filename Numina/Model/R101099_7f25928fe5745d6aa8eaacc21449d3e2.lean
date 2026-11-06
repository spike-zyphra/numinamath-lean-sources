import Mathlib

theorem algebra_278508 {x : ℝ} (hx : x^2 - 10 * x - 29 ≠ 0 ∧ x^2 - 10 * x - 45 ≠ 0 ∧ x^2 - 10 * x - 69 ≠ 0) :
    1 / (x^2 - 10 * x - 29) + 1 / (x^2 - 10 * x - 45) - 2 / (x^2 - 10 * x - 69) = 0 ↔
    x = 13 ∨ x = -3 := by
  constructor
  · -- Forward implication: if the equation is satisfied, then x is either 13 or -3.
    intro h
    rcases hx with ⟨hx1, hx2, hx3⟩
    have h1 : (x^2 - 10 * x - 45) * (x^2 - 10 * x - 69) + (x^2 - 10 * x - 29) * (x^2 - 10 * x - 69) - 2 * (x^2 - 10 * x - 29) * (x^2 - 10 * x - 45) = 0 := by
      field_simp [hx1, hx2, hx3] at h ⊢
      nlinarith
    have h4 : (x - 13) * (x + 3) = 0 := by
      nlinarith [sq_nonneg (x - 5), sq_nonneg (x - 13), sq_nonneg (x + 3)]
    cases' (mul_eq_zero.mp h4) with h5 h6
    · -- Case x = 13
      left
      linarith
    · -- Case x = -3
      right
      linarith
  · -- Backward implication: if x is either 13 or -3, then the equation is satisfied.
    rintro (h | h)
    · -- Case x = 13
      rw [h]
      norm_num
    · -- Case x = -3
      rw [h]
      norm_num