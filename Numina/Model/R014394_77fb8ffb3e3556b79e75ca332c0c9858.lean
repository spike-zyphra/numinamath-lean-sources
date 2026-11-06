import Mathlib

theorem number_theory_154665 {a b : ℕ} (ha : a > b) (h1 : a + b = 2021)
    (h2 : Nat.lcm a b = 450 * Nat.gcd a b) : a - b = 329 := by
  have h3 : b = 2021 - a := by
    omega
  rw [h3] at h2
  have h4 : a ≤ 2021 := by
    omega
  interval_cases a <;> norm_num [Nat.lcm, Nat.gcd] at h2 ⊢ <;> omega