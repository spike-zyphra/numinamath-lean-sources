import Mathlib

theorem algebra_279776 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (hxy : y = 2016 * x) (hxp : x ^ y = y ^ x) :
    Real.logb 2016 x + Real.logb 2016 y = 2017 / 2015 := by
  rw [hxy] at hxp
  have h2 : x > 0 := by linarith
  have h3 : 2016 * x > 0 := by nlinarith
  have h4 : Real.log (x ^ (2016 * x)) = Real.log ((2016 * x) ^ x) := by 
    rw [show x ^ (2016 * x) = (2016 * x) ^ x by linarith [hxp]]
  have eq2 : Real.log (x ^ (2016 * x)) = 2016 * x * Real.log x := by
    rw [Real.log_rpow]
    all_goals linarith
    all_goals linarith
  have eq3 : Real.log ((2016 * x) ^ x) = x * Real.log (2016 * x) := by
    rw [Real.log_rpow]
    all_goals linarith
    all_goals linarith
  have eq4 : Real.log x = Real.log 2016 / 2015 := by
    have h5 : Real.log (2016 * x) = Real.log 2016 + Real.log x := by
      rw [Real.log_mul (by norm_num) (by linarith)]
    rw [eq2] at h4
    rw [eq3, h5] at h4
    have h6 : 2016 * x * Real.log x = x * (Real.log 2016 + Real.log x) := by
      linarith
    have h7 : 2015 * Real.log x = Real.log 2016 := by
      nlinarith [h6, mul_pos hx (show (0 : ℝ) < (2016 : ℝ) by norm_num : (2016 : ℝ) > 0)]
    nlinarith
  have hx2 : Real.logb 2016 x = 1 / 2015 := by
    have h8 : Real.logb 2016 x = Real.log x / Real.log 2016 := by
      field_simp [Real.logb]
    rw [h8]
    rw [eq4]
    have h9 : Real.log 2016 > 0 := by
      have h10 : Real.log 2016 > 0 := by
        apply Real.log_pos
        all_goals norm_num
      linarith
    field_simp [show (0 : ℝ) < Real.log 2016 by nlinarith]
    <;> nlinarith
  have hy2 : Real.logb 2016 y = 2016 / 2015 := by
    have h9 : Real.log y = Real.log 2016 + Real.log x := by
      have h10 : y = 2016 * x := hxy
      rw [h10]
      have h11 : Real.log (2016 * x) = Real.log 2016 + Real.log x := by
        rw [Real.log_mul (by positivity) (by positivity)]
      linarith
    have h12 : Real.logb 2016 y = Real.log y / Real.log 2016 := by
      field_simp [Real.logb]
    rw [h12]
    rw [h9]
    rw [eq4]
    have h13 : Real.log 2016 > 0 := by
      apply Real.log_pos
      all_goals norm_num
    field_simp [show Real.log 2016 ≠ 0 by nlinarith]
    <;> nlinarith
    all_goals linarith
  rw [hx2, hy2]
  all_goals norm_num
  all_goals right