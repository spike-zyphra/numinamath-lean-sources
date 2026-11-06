import Mathlib

open Real Set

theorem algebra_328326 :
    IsLeast {x | ∃ t : ℝ, x = sqrt (t^2 + 4) + sqrt ((12 - t)^2 + 9)} 13 := by
  constructor
  · -- Show 13 is in the set
    use (24 / 5)
    have h1 : Real.sqrt ((24 / 5 : ℝ) ^ 2 + 4) = 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h2 : Real.sqrt ((12 - (24 / 5 : ℝ)) ^ 2 + 9) = 39 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    rw [h1, h2]
    linarith
  · -- Show 13 is the least element in the set
    intro x hx
    rcases hx with ⟨t, ht⟩
    have h1 : sqrt (t^2 + 4) + sqrt ((12 - t)^2 + 9) ≥ 13 := by
      have h1 : sqrt (t^2 + 4) ≥ 0 := Real.sqrt_nonneg (t^2 + 4)
      have h2 : sqrt ((12 - t) ^ 2 + 9) ≥ 0 := Real.sqrt_nonneg ((12 - t) ^ 2 + 9)
      have h3 : (sqrt (t^2 + 4) + sqrt ((12 - t) ^ 2 + 9)) ^ 2 ≥ 13 ^ 2 := by
        have h4 : (sqrt (t^2 + 4) + sqrt ((12 - t) ^ 2 + 9)) ^ 2 =
          (sqrt (t^2 + 4)) ^ 2 + (sqrt ((12 - t) ^ 2 + 9)) ^ 2 + 2 * (sqrt (t^2 + 4) * sqrt ((12 - t) ^ 2 + 9) ) := by ring
        have h5 : (sqrt (t^2 + 4)) ^ 2 = t^2 + 4 := Real.sq_sqrt (by nlinarith)
        have h6 : (sqrt ((12 - t) ^ 2 + 9)) ^ 2 = (12 - t)^2 + 9 := Real.sq_sqrt (by nlinarith)
        have h14 : (t^2 + 4) + ( (12 - t) ^2 + 9 ) + 2 * (sqrt (t^2 + 4) * sqrt ((12 - t) ^ 2 + 9) ) ≥ 169 := by
          nlinarith [sq_nonneg (sqrt (t^2 + 4) - 26 / 5), sq_nonneg (sqrt ((12 - t) ^ 2 + 9) - 39 / 5), 
            Real.sq_sqrt (show (t ^ 2 + 4 : ℝ) ≥ 0 by nlinarith), 
            Real.sq_sqrt (show ( (12 - t) ^ 2 + 9 : ℝ) ≥ 0 by nlinarith), 
            Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg ((12 - t) ^ 2 + 9), 
            mul_nonneg (Real.sqrt_nonneg (t^2 + 4)) (Real.sqrt_nonneg ((12 - t) ^ 2 + 9)), 
            sq_nonneg (t - 24 / 5)]
        nlinarith
        all_goals nlinarith
      nlinarith [Real.sqrt_nonneg (t^2 + 4), Real.sqrt_nonneg ((12 - t)^2 + 9)]
    linarith [ht, h1]