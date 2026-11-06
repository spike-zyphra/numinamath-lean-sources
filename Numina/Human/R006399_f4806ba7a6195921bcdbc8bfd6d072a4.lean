import Mathlib

def a: ℕ := 769

/-Let $k$ be a non-negative integer. Determine the last three digits of $769^{100k+4}$. Show the answer is 321.-/

theorem number_theory_636628 (k: ℕ): a ^ (100 * k + 4) % 1000 = 321 := by

  rw [Nat.pow_add]
  rw [Nat.mul_mod]
  suffices a ^ (100 * k) % 1000 = 1 ∧ a ^ 4 % 1000 = 321 by
    simp only [this]
  constructor
  .
    rw [show 100 * k = 50 * (2 * k) by ring]
    rw [Nat.pow_mul]
    rw [Nat.pow_mod]
    suffices a ^ 50 % 1000 = 1 by
      simp [this]
    suffices a ^ 5 % 1000 = 849 by
      rw [show a ^ 50 = (a ^ 5) ^ 10 by ring]
      rw [Nat.pow_mod]
      rw [this]
    simp [a]
  .
    simp [a]