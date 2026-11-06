import Mathlib

theorem algebra_194725 {x : ℝ} (hx : x = 1 / (2 - Real.sqrt 5)) : x^3 + 3 * x^2 - 5 * x + 1 = 0 := by
  have h1 : x = -2 - Real.sqrt 5 := by
    rw [hx]
    have h2 : (2 - Real.sqrt 5) ≠ 0 := by 
      have hsqrt5_pos : Real.sqrt 5 > 0 := Real.sqrt_pos.mpr (show (5 : ℝ) > 0 by norm_num)
      have hsqrt5_gt_2 : Real.sqrt 5 > 2 := by 
        have h1 : Real.sqrt 5 > Real.sqrt 4 := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
        have h2 : Real.sqrt 4 = (2 : ℝ) := Real.sqrt_eq_cases.mpr (by norm_num)
        linarith 
      have hne : (2 - Real.sqrt 5) ≠ 0 := by 
        intro h
        have hsqrt5_eq : Real.sqrt 5 = (2 : ℝ) := by linarith 
        have h5_eq_4 : (Real.sqrt 5) ^ 2 = 4 := by 
          rw [hsqrt5_eq]
          nlinarith [Real.sqrt_nonneg 5]
        have h5_eq_5 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
        nlinarith [Real.sqrt_nonneg 5]
        all_goals nlinarith
      exact hne 
    field_simp [h2]
    <;> ring_nf <;> nlinarith [Real.sqrt_nonneg (5 : ℝ), Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)]
  have h2 : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (show (0 : ℝ) ≤ (5 : ℝ) by norm_num)
  have h3 : Real.sqrt 5 ^ 3 = Real.sqrt 5 * 5 := by 
    calc
      Real.sqrt 5 ^ 3 = Real.sqrt 5 ^ 2 * Real.sqrt 5 := by ring
      _ = 5 * Real.sqrt 5 := by rw [h2]
      _ = Real.sqrt 5 * 5 := by ring 
  rw [h1]
  ring_nf
  <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (5 : ℝ) by norm_num), h2, h3]
  all_goals nlinarith [Real.sqrt_nonneg 5]