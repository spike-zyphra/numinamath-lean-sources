import Mathlib

open Real Set

theorem algebra_310152 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t^2 + 1) + sqrt ((4 - t)^2 + 4)} 5 := by 
  constructor
  · -- Show that 5 belongs to the set.
    use 4 / 3
    have h1 : sqrt (( (4 / 3 : ℝ) ) ^ 2 + 1) = 5 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((4 - (4 / 3 : ℝ)) ^ 2 + 4) = 10 / 3 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show that 5 is the least element in the set.
    rintro x ⟨t, ht⟩
    have h5 : sqrt (t ^ 2 + 1) + sqrt ((4 - t) ^ 2 + 4) ≥ 5 := by
      have h6 : (sqrt (t ^ 2 + 1) + sqrt ((4 - t) ^ 2 + 4)) ^ 2 ≥ 25 := by
        have h1 : (sqrt (t ^ 2 + 1)) ^ 2 = t ^ 2 + 1 := Real.sq_sqrt (by positivity)
        have h2 : (sqrt ((4 - t) ^ 2 + 4)) ^ 2 = (4 - t) ^ 2 + 4 := Real.sq_sqrt (by positivity)
        nlinarith [mul_nonneg (Real.sqrt_nonneg (t ^ 2 + 1)) (Real.sqrt_nonneg ((4 - t) ^ 2 + 4)), 
                  sq_nonneg (t - 4 / 3), 
                  sq_nonneg (sqrt (t ^ 2 + 1) - 5 / 3), 
                  sq_nonneg (sqrt ((4 - t) ^ 2 + 4) - 10 / 3), 
                  Real.sq_sqrt (show 0 ≤ (t ^ 2 + 1 : ℝ) by positivity), 
                  Real.sq_sqrt (show 0 ≤ ((4 - t) ^ 2 + 4 : ℝ) by positivity), 
                  mul_nonneg (Real.sqrt_nonneg (t ^ 2 + 1)) (Real.sqrt_nonneg ((4 - t) ^ 2 + 4))
                ]
      have h7 : sqrt (t ^ 2 + 1) + sqrt ((4 - t) ^ 2 + 4) ≥ 0 := by positivity
      nlinarith
    linarith [ht, h5]