import Mathlib

theorem number_theory_116418 (a b c d : ℕ) (h₀ : a % 6 = 4) (h₁ : b % 6 = 4) (h₂ : c % 6 = 4) (h₃ : d % 6 = 4) :
    (a + b + c + d) % 3 = 1 := by
  have ha : a % 3 = 1 := by
    omega
  have hb : b % 3 = 1 := by
    omega
  have hc : c % 3 = 1 := by
    omega
  have hd : d % 3 = 1 := by
    omega
  have hsum : (a + b + c + d) % 3 = 1 := by
    simp [Nat.add_mod, ha, hb, hc, hd]
  exact hsum