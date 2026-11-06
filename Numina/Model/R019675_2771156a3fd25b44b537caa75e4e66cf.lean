import Mathlib

theorem number_theory_13016 (n : ℕ) (hn : n > 0) :
    (3^(n + 4) - 2 * 3^(n + 2) + 2^(n + 3) - 2^n) % 7 = 0 := by
  have eq1 : 3^(n + 4) - 2 * 3^(n + 2) + 2^(n + 3) - 2^n = 7 * (9 * 3^n + 2^n) := by
    ring_nf
    <;> omega
  rw [eq1]
  simp [Nat.mul_mod]