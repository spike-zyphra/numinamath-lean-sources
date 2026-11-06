import Mathlib

theorem inequalities_174609 (x : ℝ) (hx : x > 0) :
    (x + 1) * Real.sqrt (x + 1) ≥ Real.sqrt 2 * (x + Real.sqrt x) := by
  have h1 : 0 < x := hx
  have h2 : Real.sqrt (x + 1) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith
  have h3 : Real.sqrt x > 0 := by
    apply Real.sqrt_pos.mpr
    nlinarith
  have h4 : (x + 1) * Real.sqrt (x + 1) ≥ Real.sqrt 2 * (x + Real.sqrt x) := by
    have h5 : ((x + 1) * Real.sqrt (x + 1)) ^ 2 ≥ (Real.sqrt 2 * (x + Real.sqrt x)) ^ 2 := by
      have h6 : ((x + 1) * Real.sqrt (x + 1)) ^ 2 = (x + 1) ^ 3 := by
        calc
          ((x + 1) * Real.sqrt (x + 1)) ^ 2 = (x + 1) ^ 2 * (Real.sqrt (x + 1)) ^ 2 := by
            ring
          _ = (x + 1) ^ 2 * (x + 1) := by
            rw [Real.sq_sqrt]
            nlinarith
          _ = (x + 1) ^ 3 := by
            ring
      have h7 : (Real.sqrt 2 * (x + Real.sqrt x)) ^ 2 = 2 * ((x + Real.sqrt x) ^ 2) := by
        calc
          (Real.sqrt 2 * (x + Real.sqrt x)) ^ 2 = (Real.sqrt 2) ^ 2 * ((x + Real.sqrt x) ^ 2) := by
            ring
          _ = (2) * ((x + Real.sqrt x) ^ 2) := by
            rw [Real.sq_sqrt]
            all_goals norm_num
          _ = 2 * ((x + Real.sqrt x) ^ 2) := by
            ring
      have h8 : (x + Real.sqrt x) ^ 2 = x ^ 2 + 2 * (x * (Real.sqrt x)) + x := by
        have h9 : (Real.sqrt x : ℝ) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
        nlinarith [h9]
      have h10 : (x + 1) ^ 3 ≥ 2 * ((x + Real.sqrt x) ^ 2) := by
        have h9 : (Real.sqrt x : ℝ) ^ 2 = x := Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith)
        nlinarith [Real.sqrt_nonneg x, sq_nonneg (x ^ 2 - (Real.sqrt x) ^ 2), sq_nonneg (x ^ 2 - 1), sq_nonneg ((Real.sqrt x) ^ 2 - 1), sq_nonneg (x - (Real.sqrt x)), sq_nonneg (x - 1), sq_nonneg (Real.sqrt x - 1), mul_pos h1 h3, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg (2 : ℝ)]
      nlinarith [h6, h7, h8, h10, Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (x + 1 : ℝ), Real.sqrt_nonneg (x : ℝ)]
    have h555 : (x + 1) * Real.sqrt (x + 1) ≥ Real.sqrt 2 * (x + Real.sqrt x) := by
      have h8 : (Real.sqrt 2 * (x + Real.sqrt x)) ≥ 0 := by
        positivity
      have h9 : (x + 1) * Real.sqrt (x + 1) ≥ 0 := by
        positivity
      nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sqrt_nonneg (2 : ℝ), h5, Real.sqrt_nonneg (x + 1 : ℝ), Real.sqrt_nonneg (x : ℝ), mul_nonneg (show (0 : ℝ) ≤ x + 1 by nlinarith) (show (0 : ℝ) ≤ Real.sqrt (x + 1) by positivity), mul_nonneg (show (0 : ℝ) ≤ Real.sqrt (2 : ℝ) by positivity) (show (0 : ℝ) ≤ x + Real.sqrt x by positivity)]
    exact h555
  exact h4