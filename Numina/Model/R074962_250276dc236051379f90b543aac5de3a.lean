import Mathlib

theorem algebra_65696 (total_savings : ℕ) (h : total_savings = 2 * 33 + 5 * 22) :
    total_savings - 120 = 56 := by 
  norm_num [h]