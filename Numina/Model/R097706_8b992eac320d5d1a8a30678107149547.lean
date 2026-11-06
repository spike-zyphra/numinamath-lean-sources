import Mathlib

theorem number_theory_7270 (n : ℕ) : 73 ∣ 9^(2*n+1) + 8^(n+2) := by
  induction n with
  | zero =>
    norm_num
  | succ n ih =>
    have h1 : 9^(2 * (n + 1) + 1) + 8^((n + 1) + 2) = 81 * 9^(2 * n + 1) + 8 * 8^(n + 2) := by 
      ring_nf
    rw [h1]
    omega