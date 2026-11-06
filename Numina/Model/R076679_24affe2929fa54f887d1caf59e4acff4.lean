import Mathlib

theorem number_theory_126297 (n : ℕ) :
    5 ∣ 2^(4 * n + 1) + 3^(4 * n + 1) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h1 : 2 ^ (4 * (n + 1) + 1) + 3 ^ (4 * (n + 1) + 1) =
      16 * (2 ^ (4 * n + 1)) + 81 * (3 ^ (4 * n + 1)) := by 
        ring_nf
    rw [h1]
    omega