import Mathlib

open Real

theorem algebra_311036 {a : ℝ} (ha : a = 1 / (2 + sqrt 3)) :
    sqrt (a^2 - 2 * a + 1) = sqrt 3 - 1 := by
  have ha2 : a = 2 - Real.sqrt 3 := by 
    rw [ha]
    have h1 : 2 + Real.sqrt 3 ≠ 0 := by 
      nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
    field_simp [h1]
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h2 : a ^ 2 - 2 * a + 1 = (a - 1) ^ 2 := by
    ring
  have ha3 : a - 1 = 1 - Real.sqrt 3 := by
    rw [ha2]
    ring_nf
    <;> nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  rw [h2]
  have h4 : (a - 1 : ℝ) ^ 2 = (1 - Real.sqrt 3) ^ 2 := by 
    rw [ha3]
  rw [h4]
  have h5 : sqrt (( (1 - Real.sqrt 3 : ℝ) ^ 2 )) = abs (1 - Real.sqrt 3) := by 
    rw [Real.sqrt_sq_eq_abs]
  rw [h5]
  have h6 : abs (1 - Real.sqrt 3) = Real.sqrt 3 - 1 := by 
    have h7 : 1 < Real.sqrt 3 := by 
      rw [Real.lt_sqrt]
      all_goals norm_num
    have h8 : (1 - Real.sqrt 3 : ℝ) < 0 := by 
      linarith [h7]
    rw [abs_of_neg h8]
    all_goals nlinarith
  rw [h6]
  all_goals nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]