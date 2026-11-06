import Mathlib

theorem number_theory_933 (a b : ℕ) (h₀ : a + b = 651) (h₁ : Nat.gcd a b * 108 = Nat.lcm a b) :
    (a = 84 ∧ b = 567) ∨ (a = 567 ∧ b = 84) := by
  have h2 : b = 651 - a := by 
    omega
  rw [h2] at h₁ 
  have h3 : a ≤ 651 := by 
    omega
  interval_cases a <;> norm_num [Nat.lcm, Nat.gcd] at h₁ ⊢ 
    <;> omega