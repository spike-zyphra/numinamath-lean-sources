import Mathlib
open Real

theorem algebra_252 : √(14 + 6 * √5) - √(14 - 6 * √5) = 2 * √5 := by
  have h1 : Real.sqrt (14 + 6 * Real.sqrt 5) = 3 + Real.sqrt 5 := by
    have h2 : Real.sqrt (14 + 6 * Real.sqrt 5) = Real.sqrt ((3 + Real.sqrt 5) ^ 2) := by
      have h7 : (14 + 6 * Real.sqrt 5) = (3 + Real.sqrt 5) ^ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5),
          Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h7]
    have h3 : Real.sqrt ((3 + Real.sqrt 5) ^ 2) = 3 + Real.sqrt 5 := by
      apply Real.sqrt_sq (by positivity)
    rw [h2, h3]
  have h2 : Real.sqrt (14 - 6 * Real.sqrt 5) = 3 - Real.sqrt 5 := by
    have h3 : Real.sqrt (14 - 6 * Real.sqrt 5) = Real.sqrt ((3 - Real.sqrt 5) ^ 2) := by
      have h6 : (14 - 6 * Real.sqrt 5) = (3 - Real.sqrt 5) ^ 2 := by
        nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
          mul_nonneg (Real.sqrt_nonneg 5) (Real.sqrt_nonneg 5),
          Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
      rw [h6]
    have h4 : Real.sqrt ((3 - Real.sqrt 5) ^ 2) = 3 - Real.sqrt 5 := by
      apply Real.sqrt_sq (by
        have h9 : Real.sqrt 5 < (3 : ℝ) := by
          nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num),
            Real.sqrt_nonneg 5, show √5 ^ 2 = (5 : ℝ) by
              rw [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by norm_num)]
          ]
        have h11 : (3 - Real.sqrt 5) > (0 : ℝ) := by linarith
        linarith
      )
    rw [h3, h4]
  rw [h1, h2]
  ring
  all_goals norm_num
  <;> linarith