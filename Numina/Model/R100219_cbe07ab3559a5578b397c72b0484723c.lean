import Mathlib

theorem number_theory_113571 (a b : ℕ) (h₀ : a + b = 60) (h₁ : Nat.lcm a b = 72) :
    (a, b) = (24, 36) ∨ (a, b) = (36, 24) := by
  have h2 : a ≤ 60 := by
    linarith [h₀]
  have h3 : b ≤ 60 := by
    linarith [h₀]
  interval_cases a <;> interval_cases b <;> norm_num [Nat.lcm] at h₁ ⊢ <;> 
    simp [Prod.ext_iff] at *
    <;> try tauto