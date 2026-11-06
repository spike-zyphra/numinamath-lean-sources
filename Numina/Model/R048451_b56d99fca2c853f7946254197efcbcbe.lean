import Mathlib

theorem number_theory_197979 (n : ℕ) :
    (n * (n + 1)) + ((n + 1) * (n + 2)) + (n * (n + 2)) ≠ 3000000 := by
  intro h
  have eq1 : (n * (n + 1)) + ((n + 1) * (n + 2)) + (n * (n + 2)) = 3 * n^2 + 6 * n + 2 := by
    ring_nf
    <;> omega
  rw [eq1] at h
  have h1 : (3 * n^2 + 6 * n + 2) % 3 = 2 := by
    simp [Nat.add_mod, Nat.mul_mod, pow_two]
    <;> ring_nf <;> omega
  have h2 : (3000000 : ℕ) % 3 = 0 := by
    norm_num
  omega