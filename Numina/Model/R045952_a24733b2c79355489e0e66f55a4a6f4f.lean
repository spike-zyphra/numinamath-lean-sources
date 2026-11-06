import Mathlib

theorem algebra_314433 {x : ℝ} (hx : x = 13 / (4 + Real.sqrt 3)) :
    (x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 3) / (x ^ 3 - 7 * x ^ 2 + 5 * x + 15) = -5 := by

  have h1 : Real.sqrt 3 > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h2 : 4 + Real.sqrt 3 > 0 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
  have hx2 : x = 4 - Real.sqrt 3 := by
    rw [hx]
    have h3 : 4 + Real.sqrt 3 > 0 := h2
    field_simp [(show 4 + Real.sqrt 3 ≠ 0 by linarith)]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ (3 : ℝ) by linarith)]
  have h3 : x^3 - 7 * x^2 + 5 * x + 15 = 2 := by
    rw [hx2]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (4 - Real.sqrt 3)]
  
  have h4 : x ^ 4 - 6 * x ^ 3 - 2 * x ^ 2 + 18 * x + 3 = -10 := by 
    rw [hx2]
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by linarith), sq_nonneg (Real.sqrt 3 ^ 2 - 3), sq_nonneg (4 - Real.sqrt 3)]
  
  rw [h3, h4]
  all_goals norm_num