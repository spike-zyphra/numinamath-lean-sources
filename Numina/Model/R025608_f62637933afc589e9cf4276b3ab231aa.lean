import Mathlib

theorem algebra_8174 {n : ℕ} (hn : 2^(2*n + 3) + 4^(n + 1) = 192) : n = 2 := by
  have h1 : 2 ^ (2 * n + 3) = 2 * (2 ^ (2 * n + 2)) := by
    ring_nf
  have h2 : 4 ^ (n + 1) = 2 ^ (2 * n + 2) := by
    rw [show 4 = (2 : ℕ) ^ 2 by norm_num]
    rw [← pow_mul]
    ring_nf
  rw [h1, h2] at hn
  have h3 : 3 * (2 ^ (2 * n + 2)) = 192 := by
    linarith
  have h4 : 2 ^ (2 * n + 2) = 64 := by
    omega
  have h5 : (2 * n + 2) = 6 := by
    have h6 : 2 ^ (2 * n + 2) = 2 ^ 6 := by
      rw [h4]
      norm_num
    have h7 : (2 * n + 2) = 6 := by
      exact Nat.pow_right_injective (by norm_num) h6
    exact h7
  omega