import Mathlib

theorem number_theory_93936 (ringo p : ℕ) (h₀ : ringo % 6 = 4) (h₁ : p % 6 = 3) :
    (ringo + p) % 6 = 1 := by 
  simp [Nat.add_mod, h₀, h₁]
  all_goals omega