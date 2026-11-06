import Mathlib

theorem algebra_5800 : round (((2019 * Real.sqrt 2019 - 1) / (2019 + Real.sqrt 2019 + 1)) : ℝ) = 44 := by
  have h1 : 43.5 ≤ (2019 * Real.sqrt 2019 - 1) / (2019 + Real.sqrt 2019 + 1) := by
    have h4 : Real.sqrt 2019 > 0 := by
      positivity
    have h5 : Real.sqrt 2019 ^ 2 = 2019 := Real.sq_sqrt (by norm_num)
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg 2019, Real.sq_sqrt (show 0 ≤ (2019 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2019 - 44 : ℝ), sq_nonneg (Real.sqrt 2019 - 45 : ℝ), mul_pos (show 0 < Real.sqrt 2019 by positivity) (show 0 < (2019 : ℝ) by norm_num)]
  have h2 : (2019 * Real.sqrt 2019 - 1) / (2019 + Real.sqrt 2019 + 1) < 44.5 := by
    have h4 : Real.sqrt 2019 > 0 := by
      positivity
    have h5 : Real.sqrt 2019 ^ 2 = 2019 := Real.sq_sqrt (by norm_num)
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg 2019, Real.sq_sqrt (show 0 ≤ (2019 : ℝ) by norm_num), sq_nonneg (Real.sqrt 2019 - 44 : ℝ), sq_nonneg (Real.sqrt 2019 - 45 : ℝ), mul_pos (show 0 < Real.sqrt 2019 by positivity) (show 0 < (2019 : ℝ) by norm_num)]
  rw [round_eq]
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> (try nlinarith)