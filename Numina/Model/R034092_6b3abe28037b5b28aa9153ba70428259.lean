import Mathlib

theorem inequalities_121537 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (h : a + b = 1) :
    a ^ a * b ^ b + a ^ b * b ^ a ≤ 1 := by 
  have h1 : b = 1 - a := by linarith 
  rw [show b = 1 - a by linarith]
  have h2 : a ^ a * (1 - a) ^ (1 - a) ≤ a * a + (1 - a) * (1 - a) := by 
    apply Real.geom_mean_le_arith_mean2_weighted 
    all_goals 
      nlinarith 
  have h3 : a ^ (1 - a) * (1 - a) ^ a ≤ (1 - a) * a + a * (1 - a) := by 
    apply Real.geom_mean_le_arith_mean2_weighted 
    all_goals 
      nlinarith 
  have h4 : a ^ a * (1 - a) ^ (1 - a) + a ^ (1 - a) * (1 - a) ^ a ≤ 1 := by 
    nlinarith [h2, h3, sq_nonneg (a - (1 - a)), Real.rpow_pos_of_pos ha a, Real.rpow_pos_of_pos ha (1 - a), Real.rpow_pos_of_pos (show 0 < (1 - a : ℝ) by nlinarith) a, Real.rpow_pos_of_pos (show 0 < (1 - a : ℝ) by nlinarith) (1 - a)]
  linarith