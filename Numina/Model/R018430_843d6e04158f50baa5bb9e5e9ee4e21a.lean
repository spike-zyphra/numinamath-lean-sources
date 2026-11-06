import Mathlib

open Real Set

theorem algebra_296815 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t ^ 2 + 4) + sqrt (t ^ 2 - 24 * t + 153)} 13 := by
  constructor
  · -- Show 13 is in the set
    use 24 / 5
    have h1 : Real.sqrt ((24 / 5 : ℝ) ^ 2 + 4) = 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt ((24 / 5 : ℝ) ^ 2 - 24 * (24 / 5 : ℝ) + 153) = 39 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num
  · -- Show that 13 is the minimum
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (t^2 + 4) ≥ 0 := by positivity
    have h3 : t^2 - 24 * t + 153 ≥ 0 := by 
      nlinarith [sq_nonneg (t - 12)]
    have h11 : sqrt (t ^ 2 + 4) + sqrt (t ^ 2 - 24 * t + 153) ≥ 13 := by
      have h4 : sqrt (t ^ 2 + 4) ≥ 0 := by positivity
      have h5 : sqrt (t ^ 2 - 24 * t + 153) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h13 : (sqrt (t ^ 2 + 4) + sqrt (t ^ 2 - 24 * t + 153))^2 ≥ 13^2 := by
        have h6 : (sqrt (t^2 + 4)) ^ 2 = t^2 + 4 := by 
          rw [Real.sq_sqrt]
          all_goals nlinarith
        have h7 : (sqrt (t^2 - 24 * t + 153)) ^ 2 = t^2 - 24 * t + 153 := by 
          rw [Real.sq_sqrt]
          all_goals nlinarith [show t^2 - 24 * t + 153 ≥ 0 by nlinarith]
        nlinarith [Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg (t^2 - 24 * t + 153), 
                  mul_nonneg (Real.sqrt_nonneg (t^2 + 4)) (Real.sqrt_nonneg (t^2 - 24 * t + 153)), 
                  sq_nonneg (sqrt (t^2 + 4) - sqrt (t^2 - 24 * t + 153)), 
                  sq_nonneg (t - 24 / 5)
               ]
      have h14 : sqrt (t ^ 2 + 4) + sqrt (t ^ 2 - 24 * t + 153) ≥ 0 := by 
        linarith [Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg (t^2 - 24 * t + 153)]
      nlinarith [Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg (t^2 - 24 * t + 153)]
    linarith [ht, h11]