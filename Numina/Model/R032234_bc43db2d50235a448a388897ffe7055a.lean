import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_10803 :
  IsLeast {x | ∃ a : ℝ, x = sqrt (a^2 + 9) + sqrt (a^2 - 8*a + 17)} (4*sqrt 2) := by
  constructor
  · -- 4*sqrt 2 is in the set
    use 3
    have h2 : sqrt ((3 : ℝ) ^ 2 + 9) = 3 * sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      <;> ring_nf <;> norm_num
    have h3 : sqrt ((3 : ℝ) ^ 2 - 8 * (3 : ℝ) + 17) = Real.sqrt 2 := by
      rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    rw [h2, h3]
    linarith
  · -- 4*sqrt 2 is a lower bound
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h4 : sqrt (a ^ 2 + 9) + sqrt (a ^ 2 - 8 * a + 17) ≥ 4 * Real.sqrt 2 := by
      have h5 : (sqrt (a ^ 2 + 9) + sqrt (a ^ 2 - 8 * a + 17)) ^ 2 ≥ (4 * Real.sqrt 2) ^ 2 := by
        have h6 : sqrt (a ^ 2 + 9) ≥ 0 := Real.sqrt_nonneg (a ^ 2 + 9)
        have h7 : sqrt (a ^ 2 - 8 * a + 17) ≥ 0 := Real.sqrt_nonneg (a ^ 2 - 8 * a + 17)
        have h8 : Real.sqrt 2 ≥ 0 := Real.sqrt_nonneg (2 : ℝ)
        have h9 : (4 * Real.sqrt 2) ≥ 0 := by nlinarith [Real.sqrt_nonneg 2]
        have h10 : (sqrt (a ^ 2 + 9) + sqrt (a ^ 2 - 8 * a + 17)) ^ 2 =
            (sqrt (a^2 + 9)) ^ 2 + (sqrt (a^2 - 8 * a + 17)) ^ 2 + 2 * (sqrt (a^2 + 9) * sqrt (a^2 - 8 * a + 17)) := by ring
        have h11 : (sqrt (a ^ 2 + 9)) ^ 2 = a ^ 2 + 9 := Real.sq_sqrt (by positivity)
        have h13 : a ^ 2 - 8 * a + 17 ≥ 0 := by
          nlinarith [sq_nonneg (a - 4)]
        have h12 : (sqrt (a ^ 2 - 8 * a + 17)) ^ 2 = a ^ 2 - 8 * a + 17 := by
          rw [Real.sq_sqrt]
          linarith
        rw [h10, h11, h12]
        have h15 : (4 * Real.sqrt 2) ^ 2 = 32 := by
          calc
            (4 * Real.sqrt 2) ^ 2 = 16 * (Real.sqrt 2) ^ 2 := by
              ring_nf
            _ = 16 * (2 : ℝ) := by
              rw [Real.sq_sqrt]
              all_goals norm_num
            _ = 32 := by
              norm_num
        nlinarith [sq_nonneg (sqrt (a ^ 2 + 9) - sqrt (a ^ 2 - 8 * a + 17)), sq_nonneg (a - 3), 
            Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
            mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2),
            sq_nonneg (sqrt (a ^ 2 + 9) - 4 * Real.sqrt 2), sq_nonneg (sqrt (a ^ 2 - 8 * a + 17) - Real.sqrt 2),
            Real.sqrt_nonneg (a ^ 2 + 9), Real.sqrt_nonneg (a ^ 2 - 8 * a + 17),
            mul_nonneg (Real.sqrt_nonneg (a ^ 2 + 9)) (Real.sqrt_nonneg (a ^ 2 - 8 * a + 17)), 
            sq_nonneg (a - 4)
        ]
      have h5' : sqrt (a ^ 2 + 9) + sqrt (a ^ 2 - 8 * a + 17) ≥ 0 := by positivity
      have h6' : (4 * Real.sqrt 2) ≥ 0 := by 
        nlinarith [Real.sqrt_nonneg 2]
      nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sqrt_nonneg (a ^ 2 + 9), Real.sqrt_nonneg (a ^ 2 - 8 * a + 17)]
    linarith [h4, Real.sqrt_nonneg 2, Real.sqrt_nonneg (a ^ 2 + 9), Real.sqrt_nonneg (a ^ 2 - 8 * a + 17)]