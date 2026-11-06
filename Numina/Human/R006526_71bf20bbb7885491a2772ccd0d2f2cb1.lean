import Mathlib

/-Let $N$ be a positive integer. Determine the last four digits of the number $7^{(100N + 55)}$. Show the answer is 1943.-/

theorem number_theory_638059 (N: ℕ): 7 ^ (100 * N + 55) % 10000 = 1943 := by

  rw [Nat.pow_add]
  rw [Nat.mul_mod]
  rw [show 7 ^ 55 % 10000 = 1943 by norm_num]
  suffices 7 ^ (100 * N) % 10000 = 1 by
    simp [this]
  rw [Nat.pow_mul]
  rw [Nat.pow_mod]
  suffices 7 ^ 100 % 10000 = 1 by
    simp only [this]
    clear this
    simp
  norm_num


