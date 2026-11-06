import Mathlib

theorem number_theory_9702 {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (h₀ : a^2 + b^2 = 625) (h₁ : Nat.gcd a b + Nat.lcm a b = 65) :
    a + b = 35 := by
  have h2 : a ≤ 25 := by nlinarith
  have h3 : b ≤ 25 := by nlinarith
  interval_cases a <;> interval_cases b
  <;> norm_num [Nat.gcd, Nat.lcm] at h₁ h₀ <;> all_goals
    omega