import Mathlib

theorem algebra_153569 (x : ℝ) (hx : x^6 - 2*x^5 - 9*x^4 + 14*x^3 + 24*x^2 - 20*x - 20 = 0) :
    x = Real.sqrt 2 ∨ x = -Real.sqrt 2 ∨ x = Real.sqrt 5 ∨ x = -Real.sqrt 5 ∨
    x = 1 + Real.sqrt 3 ∨ x = 1 - Real.sqrt 3 := by
  have h : (x ^ 2 - 2) * (x ^ 2 - 5) * (x ^ 2 - 2 * x - 2) = 0 := by
    nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x - 1), sq_nonneg (x ^ 2 - 2), sq_nonneg (x ^ 2 - 5), sq_nonneg (x ^ 2 - 2 * x - 2), sq_nonneg (x - Real.sqrt 2), sq_nonneg (x + Real.sqrt 2), sq_nonneg (x - Real.sqrt 5), sq_nonneg (x + Real.sqrt 5), sq_nonneg (x - (1 + Real.sqrt 3)), sq_nonneg (x - (1 - Real.sqrt 3)), Real.sqrt_pos.mpr (show 0 < (2 : ℝ) by norm_num), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sqrt_nonneg 2, Real.sqrt_nonneg 5, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h) with h1 h2
  · cases' (mul_eq_zero.mp h1) with h3 h4
    · -- x^2 - 2 = 0
      have h5 : x ^ 2 = 2 := by linarith
      have hx1 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
        have h7 : x ^ 2 = (2 : ℝ) := h5
        have h9 : x = Real.sqrt 2 ∨ x = -Real.sqrt 2 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          linarith
        tauto
      tauto
    · -- x^2 - 5 = 0
      have h6 : x ^ 2 = 5 := by linarith
      have hx4 : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
        have h7 : x ^ 2 = (5 : ℝ) := h6
        have h9 : x = Real.sqrt 5 ∨ x = -Real.sqrt 5 := by
          apply eq_or_eq_neg_of_sq_eq_sq
          norm_num
          linarith
        tauto
      tauto
  · -- x^2 - 2*x - 2 = 0
    have h7 : (x - (1 + Real.sqrt 3)) * (x - (1 - Real.sqrt 3)) = 0 := by
      nlinarith [Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num), Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h7) with h8 h9
    · -- x = 1 + Real.sqrt 3
      have h8' : x = (1 + Real.sqrt 3) := by linarith
      tauto
    · -- x = 1 - Real.sqrt 3
      have h9' : x = (1 - Real.sqrt 3) := by linarith
      tauto