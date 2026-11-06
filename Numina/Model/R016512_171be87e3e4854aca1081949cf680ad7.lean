import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_260906 {f : ℝ → ℝ} (hf : f = λ x => logb (1/4) (x^2 - 2*x - 3)) :
    MonotoneOn f {x | x < -1} := by 
  intro x hx y hy hxy
  have h1 : x < -1 := by 
    simpa using hx 
  have h2 : y < -1 := by 
    simpa using hy 
  have h3 : x ≤ y := hxy 
  have h4 : x ^ 2 - 2 * x - 3 > 0 := by 
    nlinarith 
  have h5 : y ^ 2 - 2 * y - 3 > 0 := by 
    nlinarith 
  have h6 : x ^ 2 - 2 * x - 3 ≥ y ^ 2 - 2 * y - 3 := by
    nlinarith [sq_nonneg (x + 1), sq_nonneg (y + 1), sq_nonneg (x - y)]
  have h7 : logb (1 / 4) (x ^ 2 - 2 * x - 3) ≤ logb (1 / 4) (y ^ 2 - 2 * y - 3) := by 
    have h8 : logb (1 / 4) (x ^ 2 - 2 * x - 3) = (log (x ^ 2 - 2 * x - 3) ) / (log (1 / 4)) := by 
      field_simp [logb]
    have h9 : logb (1 / 4) (y ^ 2 - 2 * y - 3) = (log (y ^ 2 - 2 * y - 3) ) / (log (1 / 4)) := by 
      field_simp [logb]
    rw [h8, h9]
    have h10 : log (1 / 4) < 0 := by
      have h11 : (1 / 4 : ℝ) < 1 := by norm_num 
      have h12 : log (1 / 4) < log (1 : ℝ) := by 
        apply Real.log_lt_log 
        all_goals linarith 
      have h13 : log (1 : ℝ) = 0 := Real.log_one 
      linarith 
    have h14 : log (x ^ 2 - 2 * x - 3) ≥ log (y ^ 2 - 2 * y - 3) := by 
      apply Real.log_le_log 
      all_goals linarith 
    have h15 : (log (x ^ 2 - 2 * x - 3)) / (log (1 / 4)) ≤ (log (y ^ 2 - 2 * y - 3)) / (log (1 / 4)) := by 
      apply (div_le_div_right_of_neg (by linarith)).mpr 
      all_goals linarith 
    linarith 
  have h8 : f x = logb (1 / 4) (x ^ 2 - 2 * x - 3) := by 
    rw [hf] 
  have h9 : f y = logb (1 / 4) (y ^ 2 - 2 * y - 3) := by 
    rw [hf] 
  rw [h8, h9]
  linarith [h7]