import Mathlib

theorem algebra_223054 {x y : ℝ} (h1 : x + y + x * y = 2 + 3 * √2) (h2 : x ^ 2 + y ^ 2 = 6) :
    (x, y) = (2, √2) ∨ (x, y) = (√2, 2) := by
  have h4 : x ^ 2 + y ^ 2 = (x + y) ^ 2 - 2 * (x * y) := by
    ring
  have eq1 : (x + y) ^ 2 - 2 * (x * y) = 6 := by
    linarith [h2, h4]
  have eq2 : x + y + x * y = 2 + 3 * √2 := h1
  have h6 : (x + y) ^ 2 + 2 * (x + y) -10 -6 * √2 = 0 := by
    have eq1' : (x + y) ^ 2 - 2 * (x * y) = 6 := by
      linarith [h2, h4]
    have eq2' : x + y + x * y = 2 + 3 * √2 := h1
    have eq7 : x * y = (2 + 3 * √2) - (x + y) := by
      linarith
    rw [eq7] at eq1'
    linarith
  have h9 : ((x + y) - (2 + Real.sqrt 2)) * ((x + y) - (-4 - Real.sqrt 2)) = 0 := by
    nlinarith [sq_nonneg ((x + y) - (2 + Real.sqrt 2)), sq_nonneg ((x + y) - (-4 - Real.sqrt 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  cases' (mul_eq_zero.mp h9) with h10 h11
  · -- Case 1: x + y = 2 + √2
    have h8 : x + y = 2 + Real.sqrt 2 := by
      linarith
    have h12 : x * y = 2 * Real.sqrt 2 := by
      nlinarith [h1, h8, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    have h13 : (x - 2) * (x - Real.sqrt 2) = 0 := by
      have h14 : y = (2 + Real.sqrt 2) - x := by
        linarith
      rw [h14] at h12
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
    cases' (mul_eq_zero.mp h13) with h14 h15
    · -- Case x = 2
      have hx : x = 2 := by linarith
      have hy : y = Real.sqrt 2 := by
        nlinarith [h8, hx, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      left
      simp [hx, hy]
    · -- Case x = √2
      have hx : x = Real.sqrt 2 := by linarith
      have hy : y = 2 := by
        nlinarith [h8, hx, Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
      right
      simp [hx, hy]
  · -- Case 2: x + y = -4 - √2
    -- This case leads to contradiction
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - (-4 - Real.sqrt 2)), sq_nonneg (x * y), sq_nonneg (x + 4 + Real.sqrt 2), sq_nonneg (y + 4 + Real.sqrt 2), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]