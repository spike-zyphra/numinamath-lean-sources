import Mathlib

theorem algebra_199749 (x : ℝ) (hx : x = Real.sqrt 2) :
    x^3 / Real.sqrt (4 - x^2) + x^2 - 4 = 0 := by 
  rw [hx]
  have h1 : (Real.sqrt 2 : ℝ) ^ 3 = 2 * Real.sqrt 2 := by
    calc
      (Real.sqrt 2 : ℝ) ^ 3 = (Real.sqrt 2 : ℝ) ^ 2 * Real.sqrt 2 := by ring
      _ = 2 * Real.sqrt 2 := by rw [Real.sq_sqrt]; positivity
  have h2 : Real.sqrt (4 - (Real.sqrt 2 : ℝ) ^ 2) = Real.sqrt 2 := by 
    have h4 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
    rw [h4]
    all_goals norm_num
  rw [h1, h2]
  have h3 : (Real.sqrt 2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  rw [h3]
  field_simp
  <;> ring_nf <;> norm_num
  <;> ring