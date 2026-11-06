import Mathlib

theorem inequalities_253974 (x y : ℝ) (h : 10 * x + 11 * y = 1 / 3) :
    x ^ 2 + y ^ 2 > 1 / 1995 := by
  have h_eq : x = (1 / 30) - (11 / 10) * y := by
    linarith
  rw [h_eq]
  have h1 : ((1 / 30 : ℝ) - (11 / 10) * y) ^ 2 + (y) ^ 2 > (1 / 1995 : ℝ) := by
    nlinarith [sq_pos_of_pos (show (0 : ℝ) < 10 by norm_num), 
      sq_pos_of_pos (show (0 : ℝ) < 11 by norm_num),
      sq_nonneg ((1 / 30 : ℝ) - (11 / 10) * y - 77 / 663), sq_nonneg (y - 11 / 663), sq_nonneg ((1 / 30 : ℝ) - (11 / 10) * (11 / 663) - (1 / 30)), sq_nonneg (y * 11 + (11 / 3) ), sq_nonneg ((10 / 3) * y - (1 / 3) * 10 / (11) * 11)]
  linarith
  all_goals try { norm_num }
  all_goals try { nlinarith }
  all_goals try { linarith }
  all_goals try { 
    norm_num at h_eq ⊢
    nlinarith 
  }
  all_goals try { 
    nlinarith 
  }
  all_goals try { 
    exfalso 
    <;> nlinarith 
  }
  <;> omega