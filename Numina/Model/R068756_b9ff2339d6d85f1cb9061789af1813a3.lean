import Mathlib

theorem number_theory_140626 {a b : ℕ} (h₀ : a / b = 4) (h₁ : a % b = 3) (h₂ : a + b + 4 + 3 = 100) :
    a = 75 := by
  have h3 : a = 4 * b + 3 := by 
    rw [←Nat.div_add_mod a b, h₀, h₁]
    all_goals omega
  omega