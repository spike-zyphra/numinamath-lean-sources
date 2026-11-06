import Mathlib

open Real

theorem inequalities_189637 {x : ℝ} (hx : x > 1) :
    2 * (sqrt (x + 1) - sqrt x) < 1 / sqrt x ∧
    1 / sqrt x < 2 * (sqrt x - sqrt (x - 1)) := by
  have h1 : 0 < sqrt x := by
    apply Real.sqrt_pos.2
    linarith
  have h3 : sqrt (x + 1) > sqrt x := Real.sqrt_lt_sqrt (by linarith) (by linarith)
  have h4 : sqrt x > sqrt (x - 1) := by
    apply Real.sqrt_lt_sqrt
    linarith
    linarith
  constructor
  · -- Prove the left inequality: 2 * (sqrt (x + 1) - sqrt x) < 1 / sqrt x
    have h5 : 0 < sqrt x := h1
    have h6 : 2 * (sqrt (x + 1) - sqrt x) < 1 / sqrt x := by
      have h7 : sqrt x > 0 := h5
      apply (lt_div_iff₀ (by positivity)).mpr
      nlinarith [Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg x, 
        mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg x), 
        sq_nonneg (sqrt (x + 1) - sqrt x), sq_nonneg (sqrt (x + 1) + sqrt x), 
        Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), Real.sq_sqrt (show 0 ≤ (x : ℝ) by linarith), 
        Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg x, 
          mul_pos (show 0 < (x : ℝ) by linarith) (show 0 < (x + 1 : ℝ) by linarith), 
          sq_nonneg (sqrt (x + 1) ^ 2 - sqrt x ^ 2)]
    exact h6
  · -- Prove the right inequality: 1 / sqrt x < 2 * (sqrt x - sqrt (x - 1))
    have h7 : 0 < sqrt x := h1
    have h8 : 1 / sqrt x < 2 * (sqrt x - sqrt (x - 1)) := by
      have h9 : sqrt x > 0 := h7
      apply (div_lt_iff₀ (by positivity)).mpr
      have h11 : 0 ≤ (x - 1 : ℝ) := by linarith
      nlinarith [Real.sqrt_nonneg x, Real.sqrt_nonneg (x - 1), 
          mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg (x - 1)), 
          sq_nonneg (sqrt x - sqrt (x - 1)), sq_nonneg (sqrt x + sqrt (x - 1)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (x - 1 : ℝ) by linarith), 
          mul_pos (show 0 < (x : ℝ) by linarith) (show 0 < (x - 1 : ℝ) by linarith), 
          sq_nonneg (sqrt x ^ 2 - sqrt (x - 1) ^ 2)]
    exact h8