import Mathlib

open Real Set

theorem algebra_2935 :
  IsLeast {y : ℝ | ∃ x : ℝ, y = sqrt (x^2 + 22 * x + 125) + sqrt (x^2 - 2 * x + 10)} 13 := by
  constructor 
  · -- Show 13 is in the set
    use (-31 / 5)
    have h1 : sqrt ((-31 / 5 : ℝ) ^ 2 + 22 * (-31 / 5) + 125) = 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((-31 / 5 : ℝ) ^ 2 - 2 * (-31 / 5) + 10) = 39 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num 
  · -- Show 13 is the least element in the set 
    intro y hy 
    rcases hy with ⟨x, hx⟩ 
    have h11 : sqrt (x^2 + 22 * x + 125) ≥ 0 := by positivity
    have h12 : sqrt (x^2 - 2 * x + 10) ≥ 0 := by positivity 
    have h13 : sqrt (x^2 + 22 * x + 125) + sqrt (x^2 - 2 * x + 10) ≥ 13 := by
      by_contra h 
      push_neg at h
      have h10 : (sqrt (x^2 + 22 * x + 125) + sqrt (x^2 - 2 * x + 10) ) < (13 : ℝ) := by linarith
      have h99 : (sqrt (x^2 + 22 * x + 125) + sqrt (x^2 - 2 * x + 10) ) ^ 2 ≥ (13 : ℝ) ^ 2 := by
        have h9 : sqrt (x^2 + 22 * x + 125) = Real.sqrt (x^2 + 22 * x + 125) := by rfl 
        have h10 : sqrt (x^2 - 2 * x + 10) = Real.sqrt (x^2 - 2 * x + 10) := by rfl 
        rw [h9, h10]
        have h11 : Real.sqrt (x^2 + 22 * x + 125) ≥ 0 := by positivity 
        have h12 : Real.sqrt (x^2 - 2 * x + 10) ≥ 0 := by positivity 
        have h13 : Real.sqrt (x^2 + 22 * x + 125) ^ 2 = x^2 + 22 * x + 125 := by 
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x + 11)]
        have h14 : Real.sqrt (x^2 - 2 * x + 10) ^ 2 = x^2 - 2 * x + 10 := by 
          rw [Real.sq_sqrt]
          nlinarith [sq_nonneg (x - 1)]
        have h15 : (Real.sqrt (x^2 + 22 * x + 125) + Real.sqrt (x^2 - 2 * x + 10) ) ^ 2 = 
          Real.sqrt (x^2 + 22 * x + 125) ^ 2 + Real.sqrt (x^2 - 2 * x + 10) ^ 2 + 2 * (Real.sqrt (x^2 + 22 * x + 125) * Real.sqrt (x^2 - 2 * x + 10) ) := by ring
        rw [h15]
        nlinarith [sq_nonneg (x + 31 / 5), Real.sqrt_nonneg (x^2 + 22 * x + 125), Real.sqrt_nonneg (x^2 - 2 * x + 10), 
          sq_nonneg ( (x + 11) / 5 - (x - 1) / 5 ), sq_nonneg (x + 31 / 5), 
          mul_nonneg (Real.sqrt_nonneg (x^2 + 22 * x + 125)) (Real.sqrt_nonneg (x^2 - 2 * x + 10)), 
          Real.mul_self_sqrt (show x^2 + 22 * x + 125 ≥ 0 by nlinarith [sq_nonneg (x + 11)]), 
          Real.mul_self_sqrt (show x^2 - 2 * x + 10 ≥ 0 by nlinarith [sq_nonneg (x - 1)]) 
          ]
      have h14 : sqrt (x^2 + 22 * x + 125) + sqrt (x^2 - 2 * x + 10) ≥ 0 := by positivity 
      have h15 : (13 : ℝ) ≥ 0 := by norm_num 
      nlinarith 
    linarith [hx, h13]