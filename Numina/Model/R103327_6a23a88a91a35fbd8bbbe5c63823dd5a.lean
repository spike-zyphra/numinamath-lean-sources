import Mathlib

theorem number_theory_12882 (a b c : ℕ) (h₀ : 0 < a) (h₁ : 0 < b) (h₂ : 0 < c)
    (h₃ : a % 12 = 7) (h₄ : b % 12 = 9) (h₅ : c % 12 = 10) :
    (a + b + c) % 12 = 2 := by 
  calc 
    (a + b + c) % 12 
        = (a % 12 + b % 12 + c % 12) % 12 := by 
          simp [Nat.add_mod, Nat.add_mod]
    _ = (7 + 9 + 10) % 12 := by 
      rw [h₃, h₄, h₅]
    _ = 26 % 12 := by 
      norm_num
    _ = 2 := by 
      norm_num