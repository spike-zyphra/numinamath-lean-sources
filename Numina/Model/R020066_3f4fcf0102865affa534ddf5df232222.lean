import Mathlib
open Real Set

/- The minimum value of the algebraic expression $\sqrt{{{x}^{2}}+4}+\sqrt{{{(12-x)}^{2}}+9}$ is ___          ___. -/
theorem algebra_1701 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (x^2 + 4) + sqrt ((12 - x)^2 + 9)} 13 := by
  constructor
  · -- Show 13 is in the set.
    use 24 / 5
    have h1 : sqrt ((24 / 5 : ℝ) ^ 2 + 4) = 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((12 - (24 / 5 : ℝ)) ^ 2 + 9) = 39 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show that 13 is the least.
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 13 := by
      have h2 : sqrt (x ^ 2 + 4) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + 4)
      have h3 : sqrt ((12 - x) ^ 2 + 9) ≥ 0 := Real.sqrt_nonneg ((12 - x) ^ 2 + 9)
      have h4 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 ≥ 13 ^ 2 := by
        have h5 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 =
            (sqrt (x ^ 2 + 4)) ^ 2 + (sqrt ((12 - x) ^ 2 + 9)) ^ 2 + 2 * (sqrt (x ^ 2 + 4) * sqrt ((12 - x) ^ 2 + 9)) := by ring
        rw [h5]
        have h6 : (sqrt (x ^ 2 + 4)) ^ 2 = x^2 + 4 := by
          rw [Real.sq_sqrt]
          positivity
        have h7 : (sqrt ((12 - x) ^ 2 + 9)) ^ 2 = (12 - x) ^ 2 + 9 := by
          rw [Real.sq_sqrt]
          positivity
        rw [h6, h7]
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 4) - sqrt ((12 - x) ^ 2 + 9) ), 
          sq_nonneg (x - 24 / 5), 
          Real.sqrt_nonneg (x^2 + 4), 
          Real.sqrt_nonneg ((12 - x)^2 + 9), 
          mul_nonneg (Real.sqrt_nonneg (x^2 + 4)) (Real.sqrt_nonneg ((12 - x)^2 + 9)), 
          Real.sq_sqrt (show (0 : ℝ) ≤ x^2 + 4 by positivity), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (12 - x)^2 + 9 by positivity)
        ]
      nlinarith [Real.sqrt_nonneg (x^2 + 4), Real.sqrt_nonneg ((12 - x)^2 + 9)]
    linarith [h1, hx]