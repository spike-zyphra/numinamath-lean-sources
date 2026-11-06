import Mathlib

theorem algebra_258923 (x : ℝ) (hx : x ≠ 3) (h : x^2 + 9 * x^2 / (x - 3)^2 = 16) :
    x = -1 + Real.sqrt 7 ∨ x = -1 - Real.sqrt 7 := by

  have h1 : x - 3 ≠ 0 := by
    intro h2
    apply hx
    linarith

  have h2 : x^2 * (x - 3)^2 + 9 * x^2 = 16 * (x - 3)^2 := by
    have h3 : x - 3 ≠ 0 := h1
    have h4 : (x - 3) ^ 2 ≠ 0 := by
      apply pow_ne_zero 2
      exact h3
    field_simp [(show x - 3 ≠ 0 by exact h3), h4] at h ⊢
    nlinarith

  have h4 : (x^2 + 2 * x - 6) * (x^2 - 8 * x + 24) = 0 := by
    nlinarith [sq_pos_of_ne_zero (show (x - 3) ≠ 0 by exact h1), sq_nonneg (x ^ 2 - 8 * x + 24), sq_nonneg (x ^ 2 + 2 * x - 6), sq_pos_of_pos (show (3 : ℝ) > 0 by norm_num), sq_nonneg (x - 3), sq_nonneg (x + 1), Real.sqrt_nonneg 7]

  cases' (mul_eq_zero.1 h4) with h5 h6
  · -- Case where $x^2 + 2x - 6 = 0$
    have h7 : (x - (-1 + Real.sqrt 7)) * (x - (-1 - Real.sqrt 7)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show (7 : ℝ) > 0 by norm_num), Real.sq_sqrt (show (7 : ℝ) ≥ 0 by norm_num)]
    cases' (mul_eq_zero.1 h7) with h8 h9
    · -- Case where $x - (-1 + \sqrt{7}) = 0$
      left
      linarith
    · -- Case where $x - (-1 - \sqrt{7}) = 0$
      right
      linarith
  · -- Case where $x^2 - 8x + 24 = 0$, which has no real solution.
    have h9 : x^2 - 8 * x + 24 = 0 := by linarith
    nlinarith [sq_nonneg (x - 4), Real.sqrt_nonneg 7]