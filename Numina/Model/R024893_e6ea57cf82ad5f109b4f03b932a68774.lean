import Mathlib

theorem number_theory_218859 (a b : ℕ) (h₀ : a + b = 378) (h₁ : Nat.gcd a b = 63) :
    (a = 63 ∧ b = 315) ∨ (a = 315 ∧ b = 63) := by 
  have h2 : a ≤ 378 := by omega 
  have h3 : b = 378 - a := by omega 
  rw [h3] at h₁
  interval_cases a <;> norm_num at h₁ ⊢ <;> omega