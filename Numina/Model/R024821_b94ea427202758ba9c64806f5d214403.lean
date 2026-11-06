import Mathlib

theorem algebra_246101 : (Real.sqrt 43 + Real.sqrt 47)^(-2 : ℤ) * (43^(-1 : ℤ) + 47^(-1 : ℤ)) +
    2 / (Real.sqrt 43 + Real.sqrt 47)^3 * (1 / Real.sqrt 43 + 1 / Real.sqrt 47) = 1 / 2021 := by
  have h1 : Real.sqrt 43 ^ 2 = 43 := Real.sq_sqrt (by norm_num)
  have h2 : Real.sqrt 47 ^ 2 = 47 := Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt 43 > 0 := by positivity
  have h4 : Real.sqrt 47 > 0 := by positivity
  have h5 : (Real.sqrt 43 + Real.sqrt 47) ^ 2 = 90 + 2 * Real.sqrt 2021 := by 
    calc
      (Real.sqrt 43 + Real.sqrt 47) ^ 2 = Real.sqrt 43 ^ 2 + Real.sqrt 47 ^ 2 + 2 * (Real.sqrt 43 * Real.sqrt 47) := by ring
      _ = 43 + 47 + 2 * (Real.sqrt 43 * Real.sqrt 47) := by rw [h1, h2]
      _ = 90 + 2 * (Real.sqrt 43 * Real.sqrt 47) := by norm_num
      _ = 90 + 2 * Real.sqrt 2021 := by
        have h6 : Real.sqrt 43 * Real.sqrt 47 = Real.sqrt 2021 := by 
          rw [← Real.sqrt_mul (by norm_num)]
          all_goals norm_num
        rw [h6]
  have h6 : Real.sqrt 43 * Real.sqrt 47 = Real.sqrt 2021 := by
    rw [← Real.sqrt_mul (by norm_num)]
    all_goals norm_num
  have h7 : (Real.sqrt 43 + Real.sqrt 47) ≠ 0 := by
    nlinarith [Real.sqrt_pos.mpr (show 0 < 43 by norm_num), Real.sqrt_pos.mpr (show 0 < 47 by norm_num)]
  have h8 : (Real.sqrt 43 + Real.sqrt 47 : ℝ) ^ (-2 : ℤ) = 1 / ((Real.sqrt 43 + Real.sqrt 47) ^ 2) := by
    simp [zpow_neg, zpow_ofNat]
  have h10 : (43 : ℝ) ^ (-1 : ℤ) = 1 / 43 := by 
    norm_num
  have h11 : (47 : ℝ) ^ (-1 : ℤ) = 1 / 47 := by
    norm_num
  have h12 : 2 / (Real.sqrt 43 + Real.sqrt 47) ^ 3 * (1 / Real.sqrt 43 + 1 / Real.sqrt 47) =
      2 * (Real.sqrt 47 + Real.sqrt 43) / (Real.sqrt 43 + Real.sqrt 47) ^ 3 / Real.sqrt 2021 := by 
    have h13 : (1 / Real.sqrt 43 + 1 / Real.sqrt 47) = (Real.sqrt 47 + Real.sqrt 43) / Real.sqrt 2021 := by
      field_simp [h1, h2, h6]
      <;> ring_nf <;> norm_num
      <;> field_simp [h1, h2, h6]
    rw [h13]
    <;> ring_nf <;> field_simp [h1, h2, h6]
  rw [h8, h10, h11]
  rw [h12]
  have h9 : (Real.sqrt 43 + Real.sqrt 47) > 0 := by 
    positivity
  field_simp [h1, h2, h7, h5, h6, h9]
  <;> ring_nf <;> norm_num
  <;> nlinarith [Real.sqrt_nonneg 43, Real.sqrt_nonneg 47, Real.sqrt_nonneg 2021, h5, Real.sq_sqrt (show (0 : ℝ) ≤ (2021 : ℝ) by norm_num)]