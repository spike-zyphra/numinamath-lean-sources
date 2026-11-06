import Mathlib

theorem algebra_214 {m : ℝ} (hm : m = Real.sqrt 5 + 1) :
    ⌊m + 1 / m⌋ = 3 := by
  rw [hm]
  have h1 : 1 / (Real.sqrt 5 + 1) = (Real.sqrt 5 - 1) / 4 := by
    field_simp [(show Real.sqrt 5 + 1 ≠ 0 by positivity)]
    <;> nlinarith [show Real.sqrt 5 ^ 2 = (5 : ℝ) by apply Real.sq_sqrt; all_goals norm_num]
  have h11 : (Real.sqrt 5 + 1 : ℝ) + (1 / (Real.sqrt 5 + 1 : ℝ)) = Real.sqrt 5 + 1 + (Real.sqrt 5 - 1) / 4 := by
    rw [h1]
    <;> ring
  rw [h11]
  have h2 : Real.sqrt 5 + 1 + (Real.sqrt 5 - 1) / 4 < (4 : ℝ) := by
    nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (5 : ℝ)]
  have h18 : 3 ≤ Real.sqrt 5 + 1 + (Real.sqrt 5 - 1) / 4 := by
    nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), Real.sqrt_nonneg (5 : ℝ), Real.sqrt_nonneg (5 : ℝ)]
  rw [Int.floor_eq_iff]
  constructor <;> ( try (nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num) ]) )