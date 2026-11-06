import Mathlib

theorem number_theory_116040 (n : ℕ) : 133 ∣ 11^(n + 2) + 12^(2 * n + 1) := by
  induction n with
  | zero =>
    norm_num
  | succ k ih =>
    have h1 : 11 ^ (k + 3) + 12 ^ (2 * (k + 1) + 1) = 11 * (11 ^ (k + 2)) + 144 * (12 ^ (2 * k + 1)) := by
      ring
    rw [h1]
    omega