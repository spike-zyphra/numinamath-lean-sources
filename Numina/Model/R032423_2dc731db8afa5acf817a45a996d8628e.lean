import Mathlib

theorem algebra_419 (d : ℝ) (h : d > 0) (h1 : 20 * d = 2 * (20 - 1) * v) (h2 : 20 * d = 2 * (20 - 1) * v + 30 / 60) :
    IsLeast {x | ∃ n, x = n * d / v ∧ 70 ≥ 5 * n + 2 * (20 - n)} 3 := by
  have eq1 : 20 * d = (38 * v : ℝ) := by 
    linarith [h1]
  have eq2 : 20 * d = (38 * v + 30 / 60 : ℝ) := by 
    linarith [h2]
  have eq3 : (0 : ℝ) = (30 / 60 : ℝ) := by
    linarith [eq1, eq2]
  norm_num at eq3 
  all_goals 
  try { 
    nlinarith [eq3]
  }
  all_goals 
  try { 
    tauto 
  }