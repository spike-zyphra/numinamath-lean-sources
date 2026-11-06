import Mathlib

open Real Set

theorem algebra_599755 :
    IsLeast {y | ∃ x : ℝ, y = sqrt (x^2 + 1) + sqrt ((4 - x)^2 + 4)} 5 := by
  constructor
  · -- Show 5 is in the set (satisfying the equality)
    use 4 / 3
    have h1 : sqrt ((4 / 3 : ℝ) ^ 2 + 1) = 5 / 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((4 - (4 / 3 : ℝ)) ^ 2 + 4) = 10 / 3 := by 
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    all_goals norm_num
  · -- Show 5 is the least element in the set (satisfying the inequality)
    intro y hy
    rcases hy with ⟨x, hx⟩
    have hx2 : sqrt (x^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4) ≥ 5 := by
      have h4 : sqrt (x ^ 2 + 1) ≥ 0 := by positivity
      have h5 : sqrt ((4 - x) ^ 2 + 4) ≥ 0 := by positivity
      have h3 : sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4) ≥ 5 := by 
        have h6 : (sqrt (x ^2 + 1) + sqrt ((4 - x) ^2 + 4)) ^ 2 ≥ 25 := by 
          have h7 : sqrt (x^ 2 + 1) ^ 2 = x ^2 + 1 := by 
            rw [Real.sq_sqrt] 
            positivity 
          have h8 : sqrt ((4 - x) ^ 2 + 4) ^ 2 = (4 - x) ^2 + 4 := by 
            rw [Real.sq_sqrt] 
            positivity 
          nlinarith [Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg ((4 - x) ^ 2 + 4), 
            sq_nonneg (sqrt (x^2 + 1) - 5 / 3), sq_nonneg (sqrt ((4 - x) ^ 2 + 4) - 10 / 3),
            sq_nonneg (x - 4 / 3), sq_nonneg ((4 - x) - 8 / 3),
            mul_nonneg (Real.sqrt_nonneg (x ^ 2 + 1)) (Real.sqrt_nonneg ((4 - x) ^2 + 4)), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (x ^ 2 + 1 : ℝ) by positivity), 
            Real.sq_sqrt (show (0 : ℝ) ≤ ((4 - x) ^ 2 + 4 : ℝ) by positivity), 
            sq_nonneg (sqrt (x ^2 + 1) ^2 - sqrt ((4 - x) ^2 + 4) ^2)
          ]
        have h12 : sqrt (x ^ 2 + 1) + sqrt ((4 - x) ^ 2 + 4) ≥ 0 := by positivity
        nlinarith [h6, Real.sqrt_nonneg (x ^ 2 + 1), Real.sqrt_nonneg ((4 - x) ^ 2 + 4)]
      linarith 
    linarith [hx2, hx]