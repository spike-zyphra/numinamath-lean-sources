import Mathlib

theorem number_theory_134067 (n : ℕ) :
    17 ∣ 2^(2*n + 3) + 3^(n + 2) * 7^n := by
  induction n with
  | zero =>
    norm_num
  | succ k ih =>
    have h1 : 2 ^ (2 * (k + 1) + 3) + 3 ^ ((k + 1) + 2) * 7 ^ (k + 1) =
      4 * (2 ^ (2 * k + 3)) + 21 * (3 ^ (k + 2) * 7 ^ k) := by
      ring_nf
    rw [h1]
    omega