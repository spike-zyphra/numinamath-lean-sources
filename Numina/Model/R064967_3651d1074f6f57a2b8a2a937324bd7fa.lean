import Mathlib

theorem number_theory_15423 (n : ℕ) (h : n % 7 = 4) :
    (n + 30) % 7 = 6 := by
  have : (n + 30) % 7 = (n % 7 + 30 % 7) % 7 := by
    simp [Nat.add_mod]
  rw [this, h]
  all_goals norm_num