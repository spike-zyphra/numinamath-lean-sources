import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_298632 {f : ℝ → ℝ}
  (hf : ∀ x, f x = x * (sqrt (36 - x ^ 2) + sqrt (64 - x ^ 2))) :
  IsGreatest (range f) 48 := by
  constructor
  · -- Show 48 is in the range
    use (24 / 5)
    rw [hf]
    have h1 : Real.sqrt (36 - (24 / 5 : ℝ) ^ 2) = (18 / 5 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : Real.sqrt (64 - (24 / 5 : ℝ) ^ 2) = (32 / 5 : ℝ) := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num
  · -- Show 48 is greatest in the range
    intro y hy 
    rcases hy with ⟨x, hx⟩ 
    have eq2 : f x = x * (sqrt (36 - x ^ 2) + sqrt (64 - x ^ 2)) := hf x 
    rw [eq2] at hx 
    have h1 : x * (sqrt (36 - x ^ 2) + sqrt (64 - x ^ 2)) ≤ 48 := by
      have h8 : sqrt (36 - x ^ 2) ≥ 0 := Real.sqrt_nonneg (36 - x ^ 2)
      have h9 : sqrt (64 - x ^ 2) ≥ 0 := Real.sqrt_nonneg (64 - x ^ 2)
      by_cases h4 : 64 - x ^ 2 < 0
      · -- Case: 64 - x^2 < 0
        have h10 : sqrt (64 - x ^ 2) = 0 := by
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith
        have h11 : sqrt (36 - x ^ 2) = 0 := by
          have h5 : 36 - x^ 2 < 0 := by
            nlinarith 
          rw [Real.sqrt_eq_zero']
          all_goals linarith
        rw [h10, h11]
        nlinarith [sq_nonneg (x ^ 2 - 40.96)]
      by_cases h4' : 36 - x^ 2 < 0 
      · -- Case: 36 - x^2 < 0
        have h10 : sqrt (36 - x ^ 2) = 0 := by 
          rw [Real.sqrt_eq_zero']
          all_goals nlinarith
        rw [h10]
        nlinarith [Real.sqrt_nonneg (64 - x^ 2), 
            Real.sq_sqrt (show 0 ≤ (64 - x ^ 2 : ℝ) by nlinarith), 
            sq_nonneg (x ^ 2 - 40.96)]
      have h4' : 36 - x^ 2 ≥ 0 := by linarith
      have h5 : 64 - x ^ 2 ≥ 0 := by linarith
      nlinarith [sq_nonneg (x - 24 / 5), sq_nonneg (sqrt (36 - x^2) - 18 / 5), sq_nonneg (sqrt (64 - x^ 2) - 32 / 5), 
          Real.sqrt_nonneg (36 - x^2), Real.sqrt_nonneg (64 - x^ 2), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (36 - x ^ 2 : ℝ) by linarith), 
          Real.sq_sqrt (show (0 : ℝ) ≤ (64 - x ^ 2 : ℝ) by linarith), 
          mul_nonneg (Real.sqrt_nonneg (36 - x^ 2)) (Real.sqrt_nonneg (64 - x^ 2))]
    have h2 : y ≤ 48 := by 
      linarith [hx, h1]
    linarith