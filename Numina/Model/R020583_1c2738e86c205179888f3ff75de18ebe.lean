import Mathlib

theorem algebra_297184 {x : ℝ} (hx : x > 0) (h : Real.logb 10 x = 1 + 2 * Real.logb 10 2 + Real.logb 10 3 / 2 - Real.logb 10 (1 / 2)) :
    x = 80 * Real.sqrt 3 := by
  have h1 : Real.logb 10 (1 / 2) = - Real.logb 10 2 := by
    simp [Real.logb_div, Real.logb_one]
  rw [h1] at h
  have h2' : Real.logb 10 10 + 3 * Real.logb 10 2 + (Real.logb 10 3 / 2) = Real.logb 10 (80 * Real.sqrt 3) := by
    have h3 : Real.logb 10 (80 : ℝ) = Real.logb 10 10 + 3 * Real.logb 10 2 := by
      have h4 : (80 : ℝ) = 10 * (2 ^ 3 : ℝ) := by norm_num
      rw [h4]
      have h5 : Real.logb 10 (10 * (2 ^ 3 : ℝ)) = Real.logb 10 (10 : ℝ) + Real.logb 10 ((2 ^ 3 : ℝ)) := by 
        rw [Real.logb_mul (by norm_num) (by norm_num)]
      have h6 : Real.logb 10 (10 : ℝ) = 1 := Real.logb_self_eq_one (by norm_num)
      have h7 : Real.logb 10 ((2 ^ 3 : ℝ)) = 3 * Real.logb 10 (2 : ℝ) := by 
        simp [Real.logb_pow]
      rw [h5, h6, h7]
    have h4 : Real.logb 10 (Real.sqrt 3) = Real.logb 10 3 / 2 := by 
      have h50 : Real.sqrt 3 > 0 := by positivity
      have h51 : Real.sqrt 3 = (3 : ℝ) ^ (1 / 2 : ℝ) := by 
        rw [Real.sqrt_eq_rpow]
      rw [h51]
      have h52 : Real.logb 10 ((3 : ℝ) ^ (1 / 2 : ℝ)) = (1 / 2 : ℝ) * Real.logb 10 (3 : ℝ) := by 
        field_simp [Real.logb_rpow_eq_mul_logb_of_pos]
      rw [h52]
      <;> ring
    have h10 : Real.logb 10 (80 * Real.sqrt 3) = Real.logb 10 (80 : ℝ) + Real.logb 10 (Real.sqrt 3) := by 
      rw [Real.logb_mul (by positivity) (by positivity)]
    rw [h10, h4, h3]
    <;> ring
  have eq2 : Real.logb 10 x = Real.logb 10 (80 * Real.sqrt 3) := by
    have eq3 : Real.logb 10 x = 1 + 2 * Real.logb 10 2 + Real.logb 10 3 / 2 + Real.logb 10 2 := by
      linarith [h]
    have h10 : 1 + 2 * Real.logb 10 2 + Real.logb 10 3 / 2 + Real.logb 10 2 = Real.logb 10 10 + 3 * Real.logb 10 2 + (Real.logb 10 3 / 2) := by 
      have h100 : Real.logb 10 10 = 1 := Real.logb_self_eq_one (by norm_num)
      linarith [h100]
    rw [eq3, h10]
    rw [h2']
  have h30 : x > 0 := by linarith
  have h31 : 80 * Real.sqrt 3 > 0 := by 
    have h300 : Real.sqrt 3 > 0 := Real.sqrt_pos.2 (by norm_num)
    nlinarith
  have h35 : x = (80 * Real.sqrt 3) := by 
    apply Real.logb_injOn_pos (by norm_num) (Set.mem_Ioi.mpr h30) (Set.mem_Ioi.mpr h31) eq2
  linarith