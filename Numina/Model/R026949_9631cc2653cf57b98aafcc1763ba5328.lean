import Mathlib

theorem number_theory_288135 (a b c : ℤ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a ≤ b + c) (h' : b ≤ a + c) (h'' : c ≤ a + b) :
    ∃ x y z, x * a + y * b + z * c = 0 := by 
  use 0, 0, 0
  all_goals 
    simp
  all_goals
    linarith