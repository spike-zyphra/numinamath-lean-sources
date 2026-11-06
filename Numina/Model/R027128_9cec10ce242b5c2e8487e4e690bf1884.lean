import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_312235 :
  IsLeast {x | ∃ t : ℝ, x = sqrt (t^2 + 4) + sqrt ((12 - t)^2 + 9)} 13 := by
  constructor
  · -- Show 13 is in the set
    use 4.8
    have h1 : sqrt (4.8 ^ 2 + 4) = (5.2 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((12 - (4.8 : ℝ)) ^ 2 + 9) = (7.8 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show that 13 is the least element in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (t^2 + 4) ≥ 0 := Real.sqrt_nonneg (t^2 + 4)
    have h2 : sqrt ((12 - t) ^ 2 + 9) ≥ 0 := Real.sqrt_nonneg ((12 - t) ^ 2 + 9)
    have h3 : sqrt (t^2 + 4) + sqrt ((12 - t) ^ 2 + 9) ≥ 13 := by
      have h4 : (sqrt (t^2 + 4) + sqrt ((12 - t) ^ 2 + 9)) ^ 2 ≥ 13 ^ 2 := by
        have h5 : (sqrt (t^2 + 4) + sqrt ((12 - t) ^ 2 + 9)) ^ 2 =
            (sqrt (t^2 + 4)) ^ 2 + (sqrt ((12 - t) ^ 2 + 9)) ^ 2 + 2 * (sqrt (t^2 + 4) * sqrt ((12 - t) ^ 2 + 9)) := by ring
        have h6 : (sqrt (t^2 + 4)) ^ 2 = t^2 + 4 := Real.sq_sqrt (show t ^ 2 + 4 ≥ 0 by nlinarith)
        have h7 : (sqrt ((12 - t) ^ 2 + 9)) ^ 2 = (12 - t)^2 + 9 := Real.sq_sqrt (show (12 - t) ^ 2 + 9 ≥ 0 by nlinarith)
        rw [h5, h6, h7]
        nlinarith [Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg ((12 - t) ^ 2 + 9), 
          sq_nonneg (sqrt (t^2 + 4) - sqrt ((12 - t) ^ 2 + 9)), sq_nonneg (t - 4.8), 
          mul_nonneg (Real.sqrt_nonneg (t^2 + 4)) (Real.sqrt_nonneg ((12 - t) ^ 2 + 9)), 
          sq_nonneg (t * (12 - t))
        ]
      nlinarith [Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg ((12 - t) ^ 2 + 9), 
          Real.sq_sqrt (show 0 ≤ t^2 + 4 by positivity), Real.sq_sqrt (show 0 ≤ (12 - t)^2 + 9 by positivity)
        ]
    linarith [ht, h3]