import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_157199 :
  IsLeast {y : ℝ | ∃ x, y = sqrt (x^2 + 4) + sqrt ((12 - x)^2 + 9)} 13 := by
  constructor
  · -- Show that 13 is in the set
    use (24 / 5)
    have h1 : sqrt ((24 / 5 : ℝ) ^ 2 + 4) = 26 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt ((12 - (24 / 5 : ℝ)) ^ 2 + 9) = 39 / 5 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2]
    norm_num
  · -- Show that 13 is minimal
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h1 : sqrt (x^2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 13 := by
      have h2 : sqrt (x ^ 2 + 4) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h3 : sqrt ((12 - x) ^ 2 + 9) ≥ 0 := by
        apply Real.sqrt_nonneg
      have h4 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 ≥ (13 : ℝ) ^ 2 := by
        have h7 : sqrt (x^2 + 4) ^2 = x^2 + 4 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h8 : sqrt ((12 - x) ^ 2 + 9) ^2 = (12 - x) ^ 2 + 9 := by
          rw [Real.sq_sqrt]
          nlinarith
        have h14 : (sqrt (x ^ 2 + 4) + sqrt ((12 - x) ^ 2 + 9)) ^ 2 =
            sqrt (x ^ 2 + 4) ^ 2 + sqrt ((12 - x) ^ 2 + 9) ^ 2 + 2 * (sqrt (x ^2 +4) * sqrt ((12 - x) ^2 + 9 )) := by
          ring
        rw [h14]
        rw [h7, h8]
        nlinarith [sq_nonneg (sqrt (x ^ 2 + 4) - 26 / 5), sq_nonneg (sqrt ((12 - x) ^ 2 + 9) - 39 / 5), 
          sq_nonneg (x - 24 / 5), 
          mul_nonneg (Real.sqrt_nonneg (x^2 + 4)) (Real.sqrt_nonneg ((12 - x) ^ 2 + 9)), 
          sq_nonneg (sqrt (x ^ 2 + 4) - 26 / 5), 
          sq_nonneg (sqrt ((12 - x) ^ 2 + 9) - 39 / 5), 
          sq_nonneg (x - 24 / 5)
        ]
      have h5 : sqrt (x^2 + 4) + sqrt ((12 - x) ^ 2 + 9) ≥ 0 := by
        nlinarith [Real.sqrt_nonneg (x^2 + 4), Real.sqrt_nonneg ((12 - x) ^ 2 + 9)]
      have h6 : (13: ℝ) ≥ 0 := by nlinarith
      nlinarith
    linarith [h1, hx]