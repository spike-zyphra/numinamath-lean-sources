import Mathlib

def is_power_less (n : ℕ) := ¬∃ k, n = k ^ 2 ∧ k > 1

theorem number_theory_239894 :
    IsLeast {n | is_power_less n} 101 ∧ IsGreatest {n | is_power_less n} 99 →
    11 ∣ (101 * 99) := by 
  intro h 
  norm_num