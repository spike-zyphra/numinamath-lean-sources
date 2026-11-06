import Mathlib

theorem algebra_310497 {x y : ℝ} (hx : x ≠ y) (h1 : x^2 + Real.sqrt 2 * y = Real.sqrt 3) (h2 : y^2 + Real.sqrt 2 * x = Real.sqrt 3) :
    y / x + x / y = 2 + 2 * Real.sqrt 3 := by
  have h3 : x^2 + Real.sqrt 2 * y = y^2 + Real.sqrt 2 * x := by
    linarith
  have h4 : (x - y) * (x + y - Real.sqrt 2) = 0 := by
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - y), sq_nonneg (x + y - Real.sqrt 2)]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- x - y = 0, so x = y contradicts hx
    exfalso
    apply hx
    linarith
  · -- x + y - Real.sqrt 2 = 0
    have h7 : x + y = Real.sqrt 2 := by linarith
    have h8 : x ≠ 0 := by
      by_contra h
      have h9 : x = 0 := by linarith
      rw [h9] at h7
      have h10 : y = Real.sqrt 2 := by linarith
      rw [h9, h10] at h1
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h9 : y ≠ 0 := by
      by_contra h
      have h10 : y = 0 := by linarith
      rw [h10] at h7
      have h11 : x = Real.sqrt 2 := by linarith
      rw [h11, h10] at h2
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]
    have h10 : x * y = 2 - Real.sqrt 3 := by
      have eq1 : x + y = Real.sqrt 2 := h7
      have eq2 : y = Real.sqrt 2 - x := by linarith
      rw [eq2] at h1
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - (Real.sqrt 2 - x)), sq_pos_of_ne_zero (show (x : ℝ) ≠ 0 by exact h8)]
    have h11 : y ^ 2 + x ^ 2 = -2 + 2 * Real.sqrt 3 := by
      have h7' : x + y = Real.sqrt 2 := h7
      have h7'' : x * y = 2 - Real.sqrt 3 := h10
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), sq_nonneg (x - y)]
    field_simp [(show x ≠ 0 by exact h8), (show y ≠ 0 by exact h9)]
    nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), h11, h10]