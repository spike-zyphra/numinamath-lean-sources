import Mathlib

theorem algebra_328358 : ⌊(Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 6) * (-Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 6) * (Real.sqrt 2 - Real.sqrt 3 + Real.sqrt 6)⌋ = 4 := by
  have h1 : 0 ≤ (Real.sqrt 2 : ℝ) := Real.sqrt_nonneg 2
  have h2 : 0 ≤ (Real.sqrt 3 : ℝ) := Real.sqrt_nonneg 3
  have h3 : 0 ≤ (Real.sqrt 6 : ℝ) := Real.sqrt_nonneg 6

  have h4 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
  have h5 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
  have h6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (show (0 : ℝ) ≤ (6 : ℝ) by norm_num)

  have h7 : (Real.sqrt 2 : ℝ) * (Real.sqrt 3 : ℝ) = Real.sqrt 6 := by
    have h8 : (Real.sqrt 2 : ℝ) * (Real.sqrt 3 : ℝ) = Real.sqrt (2 * 3) := by
      rw [← Real.sqrt_mul (by norm_num)]
    rw [h8]
    all_goals norm_num

  have h15 : ( (Real.sqrt 2 + Real.sqrt 3 - Real.sqrt 6) * (-Real.sqrt 2 + Real.sqrt 3 + Real.sqrt 6) * (Real.sqrt 2 - Real.sqrt 3 + Real.sqrt 6) ) = 7 * Real.sqrt 2 + 5 * Real.sqrt 3 - Real.sqrt 6 - 12 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), sq_nonneg (Real.sqrt 2 - Real.sqrt 3), sq_nonneg (Real.sqrt 2 - Real.sqrt 6), sq_nonneg (Real.sqrt 3 - Real.sqrt 6), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 6), mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 6), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num) ]

  rw [h15]

  have h16 : 4 ≤ 7 * Real.sqrt 2 + 5 * Real.sqrt 3 - Real.sqrt 6 - 12 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 2 - 1.4142), sq_nonneg (Real.sqrt 3 - 1.7320), sq_nonneg (Real.sqrt 6 - 2.4494), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ) ]

  have h17 : 7 * Real.sqrt 2 + 5 * Real.sqrt 3 - Real.sqrt 6 - 12 < 5 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ), Real.sq_sqrt (show (2 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (3 : ℝ) ≥ 0 by norm_num), Real.sq_sqrt (show (6 : ℝ) ≥ 0 by norm_num), sq_nonneg (Real.sqrt 2 - 1.4142), sq_nonneg (Real.sqrt 3 - 1.7320), sq_nonneg (Real.sqrt 6 - 2.4494), Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (3 : ℝ), Real.sqrt_nonneg (6 : ℝ) ]
  
  rw [Int.floor_eq_iff]
  constructor <;> (try norm_num) <;> nlinarith