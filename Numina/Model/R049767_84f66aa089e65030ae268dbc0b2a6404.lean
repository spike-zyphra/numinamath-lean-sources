import Mathlib

open Real

/- If $x>\sqrt{2}x+1$, then the value of $\left| x+\sqrt{2} \right|-\sqrt{{{(x+\sqrt{2}+1)}^{2}}}$ is ___          ___. -/
theorem inequalities_1150 (x : ℝ) (hx : x > sqrt 2 * x + 1) :
    abs (x + sqrt 2) - sqrt ((x + sqrt 2 + 1) ^ 2) = 1 := by
  have h1 : x < -1 - Real.sqrt 2 := by 
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - sqrt 2 * x - 1)]
  have h2 : (x + Real.sqrt 2) < -1 := by 
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - sqrt 2 * x - 1)]
  have h3 : (x + Real.sqrt 2) < 0 := by 
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - sqrt 2 * x - 1)]
  have h4 : abs (x + Real.sqrt 2) = -(x + Real.sqrt 2) := by
    rw [abs_of_neg]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - sqrt 2 * x - 1)]
  have h5 : (x + Real.sqrt 2 + 1) < 0 := by 
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - sqrt 2 * x - 1)]
  have h6 : sqrt ((x + Real.sqrt 2 + 1) ^ 2) = abs ((x + Real.sqrt 2 + 1)) := by 
    rw [Real.sqrt_sq_eq_abs]
  have h7 : abs ((x + Real.sqrt 2 + 1)) = -(x + Real.sqrt 2 + 1) := by
    rw [abs_of_neg]
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), sq_nonneg (x - sqrt 2 * x - 1)]
  rw [h4, h6, h7]
  linarith