import Mathlib

theorem number_theory_6156 (a b : ℕ) (hab : a = 78 ∧ b = 91) :
    Nat.lcm a b = 546 := by 
  rcases hab with ⟨ha, hb⟩
  rw [ha, hb]
  norm_num [Nat.lcm]