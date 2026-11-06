import Mathlib

theorem algebra_186675 (x : ℝ) (hx : x ≠ 0 ∧ x^2 + 1 ≠ 0) :
    (x^2 + 1)/x + x/(x^2 + 1) = 2.9 ↔ x = 2 ∨ x = 1/2 := by
  constructor
  · -- Assume (x^2 + 1)/x + x/(x^2 + 1) = 2.9, prove x = 2 ∨ x = 1/2
    intro h_eq
    have h1 : x ≠ 0 := hx.1
    have h2 : x^2 + 1 ≠ 0 := hx.2
    have h_eq1 : (x^2 + 1) ^ 2 + x^2 - 2.9 * (x^3 + x) = 0 := by
      have h_mul : x * (x^2 + 1) ≠ 0 := by
        apply mul_ne_zero
        exact h1
        exact h2
      field_simp [h1, h2] at h_eq ⊢
      nlinarith
    have h_eq2 : (x - 2) * (x - 1/2) = 0 := by
      nlinarith [h_eq1, sq_nonneg (x^2 - 1), sq_nonneg (x - 1), sq_nonneg (x + 1), sq_nonneg (x - 2), sq_nonneg (x - 1/2), sq_nonneg (x^2 - x - 1/4)]
    cases' (mul_eq_zero.mp h_eq2) with h2 h1
    · -- Case $x - 2 = 0$, so $x = 2$
      left
      linarith
    · -- Case $x - 1/2 = 0$, so $x = 1/2$
      right
      linarith
  · -- Assume x = 2 ∨ x = 1/2, prove (x^2 + 1)/x + x/(x^2 + 1) = 2.9
    rintro (h | h)
    · -- Case x = 2
      rw [h]
      norm_num
    · -- Case x = 1/2
      rw [h]
      norm_num