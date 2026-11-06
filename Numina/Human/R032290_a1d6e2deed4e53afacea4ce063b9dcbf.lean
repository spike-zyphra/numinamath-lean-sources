import Mathlib

theorem number_theory_255863 (n : ℕ) :
    19 ∣ 5^(2*n + 1) * 2^(n + 2) + 3^(n + 2) * 2^(2*n + 1) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h1 : 5 ^ (2 * (n + 1) + 1) * 2 ^ ((n + 1) + 2) + 3 ^ ((n + 1) + 2) * 2 ^ (2 * (n + 1) + 1) =
        50 * (5 ^ (2 * n + 1) * 2 ^ (n + 2)) + 12 * (3 ^ (n + 2) * 2 ^ (2 * n + 1)) := by
      ring_nf
    rw [h1]
    omega