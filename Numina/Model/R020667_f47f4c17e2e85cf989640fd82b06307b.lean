import Mathlib

theorem inequalities_598803 (x : ℝ) (hx : x ∈ Set.Icc (3 / 2) 5) :
    2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) < 2 * Real.sqrt 19 := by
  rcases hx with ⟨hx1, hx2⟩
  have h1 : 0 ≤ x + 1 := by
    linarith
  have h2 : 0 ≤ 2 * x - 3 := by
    linarith
  have h3 : 0 ≤ 15 - 3 * x := by
    linarith
  have h4 : Real.sqrt (x + 1) ≥ 0 := Real.sqrt_nonneg (x + 1)
  have h5 : Real.sqrt (2 * x - 3) ≥ 0 := Real.sqrt_nonneg (2 * x - 3)
  have h6 : Real.sqrt (15 - 3 * x) ≥ 0 := Real.sqrt_nonneg (15 - 3 * x)
  have h7 : Real.sqrt 19 ≥ 0 := Real.sqrt_nonneg 19
  have h8 : (2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x)) ^ 2 < (2 * Real.sqrt 19) ^ 2 := by
    nlinarith [sq_nonneg (2 * Real.sqrt (x + 1) - Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (2 * x - 3)), sq_nonneg (Real.sqrt (x + 1) - Real.sqrt (15 - 3 * x)), sq_nonneg (Real.sqrt (2 * x - 3) - Real.sqrt (15 - 3 * x)), 
          Real.sq_sqrt (show 0 ≤ (x + 1 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (2 * x - 3 : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (15 - 3 * x : ℝ) by linarith), 
          Real.sq_sqrt (show 0 ≤ (19 : ℝ) by norm_num), 
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (2 * x - 3)), 
          mul_nonneg (Real.sqrt_nonneg (x + 1)) (Real.sqrt_nonneg (15 - 3 * x)), 
          mul_nonneg (Real.sqrt_nonneg (2 * x - 3)) (Real.sqrt_nonneg (15 - 3 * x))
        ]
  have h9 : 2 * Real.sqrt (x + 1) + Real.sqrt (2 * x - 3) + Real.sqrt (15 - 3 * x) ≥ 0 := by
    positivity
  have h10 : (2 * Real.sqrt 19) ≥ 0 := by
    positivity
  nlinarith [Real.sqrt_nonneg (19 : ℝ), Real.sqrt_nonneg (x + 1), Real.sqrt_nonneg (2 * x - 3), Real.sqrt_nonneg (15 - 3 * x)]