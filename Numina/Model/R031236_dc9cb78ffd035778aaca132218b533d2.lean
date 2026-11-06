import Mathlib
open Real
theorem algebra_621441 : round (((4046 * √2023 - 1) / (2023 + √2023 + 1)) : ℝ) = 88 := by
  have h1 : Real.sqrt (2023 : ℝ) ≥ 0 := by positivity
  have h2 : Real.sqrt (2023 : ℝ) ^ 2 = (2023 : ℝ) := by
    exact Real.sq_sqrt (by norm_num)
  have h3 : Real.sqrt (2023 : ℝ) > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have h4 : (4046 * Real.sqrt (2023 : ℝ) - 1) / (2023 + Real.sqrt (2023 : ℝ) + 1) ≥ (87.5 : ℝ) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (2023 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2023 : ℝ) by norm_num), sq_nonneg (Real.sqrt (2023 : ℝ) - 45), sq_nonneg (Real.sqrt (2023 : ℝ) ^ 2 - 2023), Real.sqrt_nonneg (2023 : ℝ), sq_nonneg ((2023 : ℝ) - 45 ^ 2), Real.sqrt_nonneg (2023 : ℝ), mul_nonneg (Real.sqrt_nonneg (2023 : ℝ)) (Real.sqrt_nonneg (2023 : ℝ))]
  have h5 : (4046 * Real.sqrt (2023 : ℝ) - 1) / (2023 + Real.sqrt (2023 : ℝ) + 1) < (88.5 : ℝ) := by
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith [Real.sqrt_nonneg (2023 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (2023 : ℝ) by norm_num), sq_nonneg (Real.sqrt (2023 : ℝ) - 45), sq_nonneg (Real.sqrt (2023 : ℝ) ^ 2 - 2023), Real.sqrt_nonneg (2023 : ℝ), sq_nonneg ((2023 : ℝ) - 45 ^ 2), Real.sqrt_nonneg (2023 : ℝ), mul_nonneg (Real.sqrt_nonneg (2023 : ℝ)) (Real.sqrt_nonneg (2023 : ℝ))]
  rw [round_eq, Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith