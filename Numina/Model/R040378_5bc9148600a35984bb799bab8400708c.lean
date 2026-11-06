import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_298971 :
  IsLeast {x | ∃ a : ℝ, x = sqrt (a^2 - 6 * a + 10) + sqrt (a^2 + 6 * a + 13)} (3 * sqrt 5) := by
  constructor
  · -- Show 3 * sqrt 5 is in the set.
    use (1 : ℝ)
    have hx1 : (3 * sqrt 5) = sqrt (1 ^ 2 - 6 * 1 + 10) + sqrt (1 ^ 2 + 6 * 1 + 13) := by
      have h11 : sqrt (1 ^ 2 - 6 * 1 + 10) = Real.sqrt 5 := by
        norm_num
      have h22 : sqrt (1 ^ 2 + 6 * 1 + 13) = Real.sqrt 20 := by
        norm_num
      have h3 : Real.sqrt 20 = 2 * Real.sqrt 5 := by
        have h4 : (Real.sqrt 20) ^ 2 = (2 * Real.sqrt 5) ^ 2 := by
          nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 20 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num), sq_nonneg (Real.sqrt 5), sq_nonneg (Real.sqrt 20)]
        have h5 : 0 ≤ Real.sqrt 20 := Real.sqrt_nonneg 20
        have h6 : 0 ≤ (2 * Real.sqrt 5) := by nlinarith [Real.sqrt_nonneg 5, Real.sqrt_nonneg 20]
        nlinarith [h4, h5, h6]
      rw [h22, h3]
      all_goals
        nlinarith [Real.sqrt_nonneg 5, Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num)]
    linarith [hx1]
  · -- Show 3 * sqrt 5 is the least such value
    intro x hx
    rcases hx with ⟨a, ha⟩
    have h1 : sqrt (a^2 - 6 * a + 10) + sqrt (a^2 + 6 * a + 13) ≥ 3 * Real.sqrt 5 := by
      have h7 : sqrt (a ^ 2 - 6 * a + 10) + sqrt (a ^ 2 + 6 * a + 13) ≥ 0 := by
        positivity
      have h7_eq : (sqrt (a ^ 2 - 6 * a + 10)) ^ 2 = a ^ 2 - 6 * a + 10 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (a - 3)]
      have h8_eq : (sqrt (a ^ 2 + 6 * a + 13)) ^ 2 = a ^ 2 + 6 * a + 13 := by
        rw [Real.sq_sqrt]
        nlinarith [sq_nonneg (a + 3)]
      have h9 : (sqrt (a ^ 2 - 6 * a + 10) + sqrt (a ^ 2 + 6 * a + 13)) ^ 2 =
          (sqrt (a ^ 2 - 6 * a + 10)) ^ 2 + (sqrt (a ^ 2 + 6 * a + 13)) ^ 2 + 2 * (sqrt (a ^ 2 - 6 * a + 10) * sqrt (a ^ 2 + 6 * a + 13)) := by ring
      have h10 : (3 * Real.sqrt 5) ^ 2 = 45 := by
        calc
          (3 * Real.sqrt 5) ^ 2 = 9 * (Real.sqrt 5 ^ 2) := by ring
          _ = 9 * 5 := by rw [Real.sq_sqrt (show 0 ≤ 5 by norm_num)]
          _ = 45 := by norm_num
      have h11 : (sqrt (a ^ 2 - 6 * a + 10) + sqrt (a ^ 2 + 6 * a + 13)) ^ 2 ≥ (3 * Real.sqrt 5) ^ 2 := by
        have h12 : (sqrt (a ^ 2 - 6 * a + 10) + sqrt (a ^ 2 + 6 * a + 13)) ^ 2 - (3 * Real.sqrt 5) ^ 2 ≥ 0 := by
          nlinarith [Real.sqrt_nonneg (a ^ 2 - 6 * a + 10), Real.sqrt_nonneg (a ^ 2 + 6 * a + 13), 
            Real.sqrt_nonneg 5, sq_nonneg (a ^ 2 - 6 * a + 10 - (a ^ 2 + 6 * a + 13)), sq_nonneg (a - 1), sq_nonneg (sqrt (a ^ 2 - 6 * a + 10) - sqrt (a ^ 2 + 6 * a + 13)), 
            sq_nonneg (a + 3), sq_nonneg (a - 3), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 - 6 * a + 10) by nlinarith [sq_nonneg (a - 3)]), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + 6 * a + 13) by nlinarith [sq_nonneg (a + 3)]), 
            Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
            mul_nonneg (Real.sqrt_nonneg (a ^ 2 - 6 * a + 10)) (Real.sqrt_nonneg (a ^ 2 + 6 * a + 13))
          ]
        linarith
      nlinarith [Real.sqrt_nonneg (a ^ 2 - 6 * a + 10), Real.sqrt_nonneg (a ^ 2 + 6 * a + 13), 
        Real.sqrt_nonneg 5, sq_nonneg (a ^ 2 - 6 * a + 10 - (a ^ 2 + 6 * a + 13)), sq_nonneg (a - 1), sq_nonneg (sqrt (a ^ 2 - 6 * a + 10) - sqrt (a ^ 2 + 6 * a + 13)), 
        sq_nonneg (a + 3), sq_nonneg (a - 3), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 - 6 * a + 10) by nlinarith [sq_nonneg (a - 3)]), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (a ^ 2 + 6 * a + 13) by nlinarith [sq_nonneg (a + 3)]), 
        Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num), 
        mul_nonneg (Real.sqrt_nonneg (a ^ 2 - 6 * a + 10)) (Real.sqrt_nonneg (a ^ 2 + 6 * a + 13))
      ]
    linarith [ha, h1]