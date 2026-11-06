import Mathlib

theorem algebra_204907 :
    {x | (x^2 - x + 1)^4 - 10 * x^2 * (x^2 - x + 1)^2 + 9 * x^4 = 0} =
    {-1 ,1 ,2 - Real.sqrt 3 ,2 + Real.sqrt 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Forward implies: from the equation prove the four roots
    intro h
    have h1 : (x^2 - x + 1)^4 - 10 * x^2 * (x^2 - x + 1)^2 + 9 * x^4 = 0 := by
      linarith
    have h2 : ((x ^ 2 - x + 1) ^ 2 - 9 * x^2) * ((x ^ 2 - x + 1) ^ 2 - x^2) = 0 := by
      nlinarith [h1]
    cases' (mul_eq_zero.1 h2) with h3 h4
    · -- ((x ^ 2 - x + 1) ^ 2 - 9 * x^2) = 0
      have h3' : (x ^ 2 - x + 1) ^ 2 = 9 * x^2 := by linarith
      have h5 : (x ^ 2 - x + 1 - 3 * x) * (x ^ 2 - x + 1 + 3 * x) = 0 := by
        nlinarith [h3']
      cases' (mul_eq_zero.1 h5) with h6 h7
      · 
        have h6' : x^2 - 4 * x + 1 = 0 := by
          nlinarith [h6]
        have h8 : (x - (2 - Real.sqrt 3)) * (x - (2 + Real.sqrt 3)) = 0 := by
          nlinarith [h6', Real.sqrt_pos.mpr (show 0 < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show 0 ≤ 3 by norm_num : (0 : ℝ) ≤ 3)]
        cases' (mul_eq_zero.1 h8) with h9 h10
        · 
          right 
          right 
          left 
          linarith 
        · 
          right 
          right 
          right 
          linarith 
      · 
        have h7' : (x + 1) ^ 2 = 0 := by
          nlinarith [h7]
        have h8 : x + 1 = 0 := by
          apply pow_eq_zero 
          exact h7'
        have h9 : x = -1 := by linarith 
        left 
        simp [h9]
    · -- ((x ^ 2 - x + 1) ^ 2 - x^2) = 0
      have h4' : (x ^ 2 - x + 1) ^ 2 = x^2 := by linarith 
      have h5 : (x ^ 2 - 2 * x + 1) * (x ^ 2 + 1) = 0 := by
        nlinarith [h4']
      cases' (mul_eq_zero.1 h5) with h6 h7
      · -- x^2 - 2x + 1 = 0 
        have h6' : (x - 1) ^ 2 = 0 := by
          nlinarith [h6]
        have h7 : x - 1 = 0 := by
          apply pow_eq_zero 
          exact h6'
        have h8 : x = 1 := by linarith 
        right 
        left 
        simp [h8]
      · -- x^2 + 1 = 0 
        nlinarith [sq_nonneg x]
  · -- Backward direction: from the roots prove the equation
    rintro (h | h | h | h)
    · -- x = -1
      rw [h]
      norm_num
    · -- x = 1
      rw [h]
      norm_num
    · -- x = 2 - Real.sqrt 3
      rw [h]
      have h20 : ((2 - Real.sqrt 3) ^ 2 - (2 - Real.sqrt 3) + 1) ^ 2 = 9 * ((2 - Real.sqrt 3)  ) ^ 2 := by
        nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg ((2 - Real.sqrt 3 : ℝ) ) ]
      nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg ((2 - Real.sqrt 3 : ℝ) ) ]
    · -- x = 2 + Real.sqrt 3
      rw [h]
      have h130 : ((2 + Real.sqrt 3 : ℝ) ^ 2 - (2 + Real.sqrt 3 : ℝ) + 1 : ℝ) ^ 2 = 9 * ((2 + Real.sqrt 3 : ℝ) ) ^ 2 := by
        nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg ((2 + Real.sqrt 3 : ℝ) ) ]
      nlinarith [ Real.sqrt_pos.mpr (show (0 : ℝ) < 3 by norm_num : (0 : ℝ) < 3), Real.sq_sqrt (show (0 : ℝ) ≤ (3 : ℝ) by norm_num : (0 : ℝ) ≤ (3 : ℝ)), sq_nonneg ((2 + Real.sqrt 3 : ℝ) ) ]