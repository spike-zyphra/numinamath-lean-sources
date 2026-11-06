import Mathlib

theorem number_theory_197174 :
    ∃ a b, a + b = 168 ∧ Nat.gcd a b = 24 := by
  exact ⟨24, 144, by norm_num, by norm_num⟩