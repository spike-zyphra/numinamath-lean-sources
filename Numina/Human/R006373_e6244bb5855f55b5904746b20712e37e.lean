import Mathlib

/- Let $k$ be a positive integer.
Determine the first (most significant) digit of the product $(10^k - 1) \times (5 \cdot 10^k - 1)$.
Show the answer is 4.-/

theorem number_theory_636392 (k: ℕ) (h: 0 < k):
  4 * 10 ^ (2 * k) ≤ (10 ^ k - (1: ℤ)) * (5 * 10 ^ k - 1) ∧ (10 ^ k - 1) * (5 * 10 ^ k - (1: ℤ)) < 5 * 10 ^ (2 * k) := by

  rw [show (10: ℤ) ^ (2 * k) = (10 ^ k) ^ 2 by ring]
  set t:= (10: ℤ) ^ k
  have lt: 10 ≤ t := by
    simp [t]
    nth_rewrite 1 [show (10: ℤ) = 10 ^ 1 by rfl]
    apply pow_le_pow_right₀
    norm_num
    omega
  clear_value t
  constructor
  .
    ring_nf
    nlinarith
  .
    ring_nf
    nlinarith
