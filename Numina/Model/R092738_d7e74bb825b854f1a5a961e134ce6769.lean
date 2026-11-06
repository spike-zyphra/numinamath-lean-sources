import Mathlib

theorem number_theory_126463 (n : ℕ) (h : 9 ∣ (10^n + 1)) : 9 ∣ (10^(n + 1) + 1) := by
  have h1 : 10 ^ (n + 1) + 1 = 9 * (10 ^ n) + (10 ^ n + 1) := by
    ring
  rw [h1]
  have h2 : 9 ∣ 9 * (10 ^ n) := by 
    use (10 ^ n)
    all_goals ring
  have h3 : 9 ∣ (9 * (10 ^ n) + (10 ^ n + 1)) := by
    apply Nat.dvd_add
    exact h2
    exact h
  exact h3