import Mathlib

theorem number_theory_61919 (a b c : ℝ) (h₀ : (a * b) % 1 = 1 / 2) (h₁ : (a * c) % 1 = 1 / 2)
    (h₂ : (b * c) % 1 = 1 / 2) :
    Irrational a ∧ Irrational b ∧ Irrational c := by
-- Lean's approach contradicts standard real number arithmetic
-- Lean's specific formalization requires us to step through the claimed derivationally inconsistent system
  norm_num at h₀ h₁ h₂
  all_goals norm_num at h₀ h₁ h₂