import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_177201 :
  IsGreatest {x | ∃ a b c : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ a + b + c = 3 ∧ x = sqrt a + sqrt (2*b + 2) + sqrt (3*c + 6)} 6 := by
  constructor
  · -- Show 6 is in the set
    use 1, 1, 1
    constructor
    · norm_num -- 1 > 0
    constructor
    · norm_num -- 1 > 0
    constructor
    · norm_num -- 1 > 0
    constructor
    · norm_num -- 1 + 1 + 1 = 3
    have h1 : sqrt (1 : ℝ) = 1 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h2 : sqrt (2 * (1 : ℝ) + 2) = 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    have h3 : sqrt (3 * (1 : ℝ) + 6) = 3 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h1, h2, h3]
    all_goals norm_num
  · -- Show 6 is greatest in the set
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, hx⟩
    have h2 : sqrt a + sqrt (2 * b + 2) + sqrt (3 * c + 6) ≤ 6 := by
      nlinarith [sq_nonneg (sqrt a - 1), sq_nonneg (sqrt (2 * b + 2) - 2), sq_nonneg (sqrt (3 * c + 6) - 3),
          Real.sqrt_nonneg a, Real.sqrt_nonneg (2 * b + 2), Real.sqrt_nonneg (3 * c + 6),
          Real.sq_sqrt (show (0 : ℝ) ≤ a by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ (2 * b + 2) by nlinarith), Real.sq_sqrt (show (0 : ℝ) ≤ (3 * c + 6) by nlinarith),
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (2 * b + 2)), 
          mul_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg (3 * c + 6)), 
          mul_nonneg (Real.sqrt_nonneg (2 * b + 2)) (Real.sqrt_nonneg (3 * c + 6))
      ]
    linarith [h2, hx]