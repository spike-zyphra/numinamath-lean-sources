import Mathlib

theorem number_theory_2702 {x : ℕ} (hx : x * 50 > 3193) (h : x * (3193 / 50) = 3193) :
    x = 103 ∧ (3193 / 50) = 0.31 := by
  norm_num at h
  all_goals
  try { linarith }
  all_goals
  try { 
    omega
  }