import Mathlib

theorem algebra_22357 {x : ℝ}
    (hx : x = Real.sqrt (104 * Real.sqrt 6 + 468 * Real.sqrt 10 + 144 * Real.sqrt 15 + 2006)) :
    ∃ a b c : ℕ, a > 0 ∧ b > 0 ∧ c > 0 ∧ x = a * Real.sqrt 2 + b * Real.sqrt 3 + c * Real.sqrt 5 ∧ a * b * c = 936 := by 
  have h1 : Real.sqrt 6 = Real.sqrt 2 * Real.sqrt 3 := by 
    calc 
      Real.sqrt 6 = Real.sqrt (2 * 3) := by norm_num 
      _ = Real.sqrt 2 * Real.sqrt 3 := by rw [Real.sqrt_mul (by norm_num)] 
  have h2 : Real.sqrt 10 = Real.sqrt 2 * Real.sqrt 5 := by 
    calc 
      Real.sqrt 10 = Real.sqrt (2 * 5) := by norm_num 
      _ = Real.sqrt 2 * Real.sqrt 5 := by rw [Real.sqrt_mul (by norm_num)] 
  have h3 : Real.sqrt 15 = Real.sqrt 3 * Real.sqrt 5 := by 
    calc 
      Real.sqrt 15 = Real.sqrt (3 * 5) := by norm_num 
      _ = Real.sqrt 3 * Real.sqrt 5 := by rw [Real.sqrt_mul (by norm_num)] 
  use 13, 4, 18 
  constructor 
  · norm_num 
  constructor 
  · norm_num 
  constructor 
  · norm_num 
  constructor 
  · -- Show x = 13 * Real.sqrt 2 + 4 * Real.sqrt 3 + 18 * Real.sqrt 5 
    rw [hx] 
    have h4 : (13 * Real.sqrt 2 + 4 * Real.sqrt 3 + 18 * Real.sqrt 5 : ℝ) ^ 2 = 104 * Real.sqrt 6 + 468 * Real.sqrt 10 + 144 * Real.sqrt 15 + 2006 := by 
      rw [h1, h2, h3]
      nlinarith [Real.sqrt_nonneg 2, Real.sqrt_nonneg 3, Real.sqrt_nonneg 5,
          Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), 
          Real.sq_sqrt (show (0 : ℝ) ≤ 5 by norm_num),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 3),
          mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 5),
          mul_nonneg (Real.sqrt_nonneg 3) (Real.sqrt_nonneg 5)]
    have h5 : Real.sqrt (104 * Real.sqrt 6 + 468 * Real.sqrt 10 + 144 * Real.sqrt 15 + 2006) = 13 * Real.sqrt 2 + 4 * Real.sqrt 3 + 18 * Real.sqrt 5 := by 
      rw [←h4]
      field_simp 
    rw [h5]
    all_goals norm_num
  · -- Show a * b * c = 936 
    norm_num