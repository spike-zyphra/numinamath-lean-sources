import Mathlib

theorem number_theory_278579 (a b : ℕ) (h₀ : a = 2020) (h₁ : b ≠ 0) (h₂ : a / b = 106) (h₃ : a % b = 6) :
    (2002 / b = 105) := by
  have h4 : a = 106 * b + 6 := by 
    rw [←Nat.div_add_mod a b, h₂, h₃]
    all_goals omega
  rw [h₀] at h4
  have h5 : 106 * b = 2014 := by
    omega
  have h6 : b = 19 := by 
    omega
  subst h6
  all_goals norm_num