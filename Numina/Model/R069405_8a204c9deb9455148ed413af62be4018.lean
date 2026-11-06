import Mathlib

theorem algebra_4408 {x : ℝ} (hx : x = - 3 / (2 + Real.sqrt 5)) :
    Real.sqrt (x^3 - 12 * x^2 - 9 * x + 81) = 9 := by
  have h1 : x = 6 - 3 * Real.sqrt 5 := by
    rw [hx]
    -- Multiply by conjugate
    have h2 : (2 + Real.sqrt 5) ≠ 0 := by 
      by_contra h 
      have h5 : Real.sqrt 5 = -2 := by 
        nlinarith 
      nlinarith [Real.sqrt_nonneg 5, Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5] 
    field_simp [h2]
    <;> ring_nf
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (√5 - 2), sq_nonneg (√5 * 3 - 6)]
  have h2 : x^3 - 12 * x^2 - 9 * x + 81 = (81 : ℝ) := by
    rw [h1]
    --Use algebra to compute
    nlinarith [pow_nonneg (Real.sqrt_nonneg 5) 3, sq_nonneg (√5 - 2), sq_nonneg (√5 - 3), Real.sqrt_pos.mpr (show 0 < (5 : ℝ) by norm_num : (5 : ℝ) > 0), Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num : (0 : ℝ) ≤ (5 : ℝ)), sq_nonneg (√5 * 3 * 2 - 6)]
  rw [h2]
  exact Real.sqrt_eq_cases.mpr (by norm_num)