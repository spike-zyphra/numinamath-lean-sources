import Mathlib

theorem algebra_161243 {x : ℝ} (hx : x^3 = 26 + 15 * Real.sqrt 3) :
    x * (2 - Real.sqrt 3) = 1 := by
  have h1 : x^3 - (26 + 15 * Real.sqrt 3) = 0 := by linarith
  have h2 : (2 + Real.sqrt 3)^3 = 26 + 15 * Real.sqrt 3 := by
    ring_nf
    have h1 : (Real.sqrt 3 : ℝ) ^ 2 = 3 := Real.sq_sqrt (show 0 ≤ 3 by norm_num)
    have h2 : (Real.sqrt 3 : ℝ) ^ 3 = Real.sqrt 3 * 3 := by
      calc
        (Real.sqrt 3 : ℝ) ^ 3 = (Real.sqrt 3 : ℝ) ^ 2 * Real.sqrt 3 := by ring
        _ = 3 * Real.sqrt 3 := by rw [h1]
        _ = Real.sqrt 3 * 3 := by ring
    simp [h1, h2]
    <;> ring_nf <;> norm_num
    <;> ring
  have h3 : x^3 - (2 + Real.sqrt 3)^3 = 0 := by
    rw [h2] at *
    linarith
  have h4 : (x - (2 + Real.sqrt 3)) * (x^2 + (2 + Real.sqrt 3) * x + (2 + Real.sqrt 3)^2) = 0 := by
    ring_nf at h3 ⊢
    nlinarith [sq_nonneg (x^2), sq_nonneg (x + (2 + Real.sqrt 3)), sq_nonneg (x - (2 + Real.sqrt 3)), sq_nonneg (Real.sqrt 3), Real.sqrt_pos.mpr (show 0 < (3:ℝ) by norm_num : (3:ℝ) > 0), Real.sq_sqrt (show 0 ≤ (3:ℝ) by norm_num : (3:ℝ) ≥ 0)]
  cases' (mul_eq_zero.mp h4) with h5 h6
  · -- Case x - (2 + \sqrt{3}) = 0, so x = 2 + \sqrt{3}
    have hx_eq : x = 2 + Real.sqrt 3 := by linarith
    rw [hx_eq]
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num), Real.sqrt_pos.mpr (show (0 : ℝ) < (3 : ℝ) by norm_num), sq_nonneg (Real.sqrt 3)]
  · -- Case x^2 + (2 + \sqrt{3}) * x + (2 + \sqrt{3})^2 = 0
    have h7 : x^2 + (2 + Real.sqrt 3) * x + (2 + Real.sqrt 3)^2 = 0 := by linarith
    nlinarith [sq_nonneg (x + (2 + Real.sqrt 3) / 2), sq_nonneg (Real.sqrt 3), sq_pos_of_pos (Real.sqrt_pos.mpr (show 0 < (3 : ℝ) by norm_num)), sq_nonneg (x^2), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)]