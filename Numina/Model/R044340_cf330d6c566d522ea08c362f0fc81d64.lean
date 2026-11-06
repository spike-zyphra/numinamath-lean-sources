import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_313868 :
  IsLeast {x | ∃ t : ℝ, x = sqrt (t^2 + 1) + sqrt ((t - 12)^2 + 16)} 13 := by
  constructor
  · -- Show 13 is in the set
    use 12 / 5
    have h1 : sqrt ((12 / 5 : ℝ) ^ 2 + 1) = 13 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((12 / 5 - 12 : ℝ) ^ 2 + 16) = 52 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show 13 is the minimum value
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (t ^ 2 + 1) ≥ 0 := by positivity
    have h2 : sqrt ((t - 12) ^ 2 + 16) ≥ 0 := by positivity
    have h3 : sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16) ≥ 13 := by
      have h7 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 ≥ 169 := by
        have h11 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 ≥ 169 := by
          have h15 : sqrt (t ^ 2 + 1) ^ 2 = t ^ 2 + 1 := Real.sq_sqrt (show t ^ 2 + 1 ≥ 0 by positivity)
          have h16 : sqrt ((t - 12) ^ 2 + 16) ^ 2 = (t - 12) ^ 2 + 16 := Real.sq_sqrt (show (t - 12) ^ 2 + 16 ≥ 0 by positivity)
          have h14 : (sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16)) ^ 2 = 
            (sqrt (t ^ 2 + 1) ^ 2) + (sqrt ((t - 12) ^ 2 + 16) ^ 2) + 2 * (sqrt (t ^ 2 + 1) * sqrt ((t - 12) ^ 2 + 16)) := by ring
          rw [h14, h15, h16]
          nlinarith [sq_nonneg (t - 12 / 5), sq_nonneg (sqrt (t ^ 2 + 1) - 13 / 5), sq_nonneg (sqrt ((t - 12) ^ 2 + 16) - 52 / 5), 
            mul_nonneg (Real.sqrt_nonneg (t ^ 2 + 1)) (Real.sqrt_nonneg ((t - 12) ^ 2 + 16)), 
            Real.sq_sqrt (show (t^2 + 1 : ℝ) ≥ 0 by positivity), 
            Real.sq_sqrt (show ((t - 12) ^ 2 + 16 : ℝ) ≥ 0 by positivity), 
            sq_nonneg (t ^ 2 - (t -12) ^ 2)
          ]
        nlinarith [Real.sqrt_nonneg (t ^ 2 + 1), Real.sqrt_nonneg ((t - 12) ^ 2 + 16)]
      have h4 : sqrt (t ^ 2 + 1) + sqrt ((t - 12) ^ 2 + 16) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (t ^ 2 + 1), Real.sqrt_nonneg ((t - 12) ^ 2 + 16), h7]
    linarith [ht, h3]