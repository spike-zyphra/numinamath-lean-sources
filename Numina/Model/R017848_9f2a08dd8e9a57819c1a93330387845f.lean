import Mathlib

theorem number_theory_258600 (y : ℕ) (hy : y < 1960) (h : 1960 - y = (Nat.digits 10 y).sum) :
    1960 - y = 17 := by
  interval_cases y <;> norm_num at h ⊢ <;> all_goals omega