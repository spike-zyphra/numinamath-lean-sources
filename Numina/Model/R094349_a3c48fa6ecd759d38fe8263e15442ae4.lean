import Mathlib

theorem algebra_1621 {x : ℕ} : 44 * 25 = x * 100 ↔ x = 11 := by 
  constructor
  · -- Assume 44 * 25 = x * 100, prove x = 11
    intro h
    have h1 : x = 11 := by 
      omega
    exact h1
  · -- Assume x = 11, prove 44 * 25 = x * 100
    intro h
    subst h
    all_goals norm_num