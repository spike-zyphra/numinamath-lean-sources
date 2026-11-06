import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_147438 :
  IsLeast {y | ∃ x : ℝ, y = sqrt ((1/4)*x^4 - 2*x^2 - 4*x + 13) + (1/2)*x^2 + (1/2)} (7/2) := by 
  constructor
  · -- Show 7/2 is in the set
    use 2
    have h1 : sqrt ((1 / 4) * (2 : ℝ) ^ 4 - 2 * (2 : ℝ) ^ 2 - 4 * (2 : ℝ) + 13) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1]
    norm_num
  · -- Show 7/2 is minimal
    intro y hy
    rcases hy with ⟨x, hx⟩
    have h2 : sqrt ((1 / 4) * x ^ 4 - 2 * x ^ 2 - 4 * x + 13) + (1 / 2) * x ^ 2 + (1 / 2) ≥ 7 / 2 := by
      have h3 : sqrt ((1 / 4) * x ^ 4 - 2 * x ^ 2 - 4 * x + 13) ≥ 3 - (1 / 2) * x ^ 2 := by
        by_cases h : 3 - (1 / 2) * x ^ 2 ≤ 0
        · -- Case where 3 - (1/2)x^2 ≤0
          have h4 : sqrt ((1 / 4) * x ^ 4 - 2 * x ^ 2 - 4 * x + 13) ≥ 0 := by positivity
          nlinarith
        · -- Case where 3 - (1/2)x^2 >0
          have h6 : (1 / 4) * x ^ 4 - 2 * x ^ 2 - 4 * x + 13 ≥ (3 - (1 / 2) * x ^ 2) ^ 2 := by
            nlinarith [sq_nonneg (x - 2)]
          have h7 : sqrt ((1 / 4) * x ^ 4 - 2 * x ^ 2 - 4 * x + 13) ≥ sqrt ((3 - (1 / 2) * x ^ 2) ^ 2) := by
            apply Real.sqrt_le_sqrt
            linarith
          have h8 : sqrt ((3 - (1 / 2) * x ^ 2) ^ 2) = abs (3 - (1 / 2) * x ^ 2) := by
            rw [Real.sqrt_sq_eq_abs]
          have h9 : abs (3 - (1 / 2) * x ^ 2) = 3 - (1 / 2) * x ^ 2 := by
            rw [abs_of_nonneg (show 0 ≤ 3 - (1 / 2) * x ^ 2 by nlinarith [h] ) ]
          rw [h8, h9] at h7
          linarith
      nlinarith [h3]
    linarith [h2, hx]