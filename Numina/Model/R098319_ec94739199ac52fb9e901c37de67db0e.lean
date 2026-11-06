import Mathlib

theorem number_theory_3865
    (p q : ℕ)
    (h₀ : Nat.Prime p)
    (h₁ : Nat.Prime q)
    (h₂ : 19 * p + 23 * q = 429) :
    p + q = 19 := by
  have h3 : p ≤ 22 := by
    omega
  have h4 : q ≤ 18 := by
    omega
  interval_cases q <;> interval_cases p <;> norm_num at h₂ h₀ h₁ ⊢ <;> all_goals try { tauto }