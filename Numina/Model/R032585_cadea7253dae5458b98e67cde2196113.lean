import Mathlib

theorem number_theory_3216 (N : ℕ) (hN : N > 0) (hN1 : N^2 = 25^64 * 64^25) : (Nat.digits 10 N).sum = 14 := by
  have h1 : N^2 = 25^64 * 64^25 := hN1
  have h2 : N ^ 2 = 2 ^ 150 * 5 ^ 128 := by
    norm_num at h1 ⊢
    all_goals
      nlinarith
  have h3 : N = 2 ^ 75 * 5 ^ 64 := by
    have h4 : N ^ 2 = 2 ^ 150 * 5 ^ 128 := h2
    have h5 : N = 2 ^ 75 * 5 ^ 64 := by
      have h6 : N ^ 2 = (2 ^ 75 * 5 ^ 64) ^ 2 := by
        nlinarith [h4]
      have h7 : N = 2 ^ 75 * 5 ^ 64 := by
        nlinarith [sq_nonneg (N - (2 ^ 75 * 5 ^ 64) : ℕ), hN]
      exact h7
    exact h5
  have h8 : N = 2 ^ 11 * 10 ^ 64 := by
    calc
      N = 2 ^ 75 * 5 ^ 64 := h3
      _ = 2 ^ 11 * 2 ^ 64 * 5 ^ 64 := by
        ring_nf
      _ = 2 ^ 11 * (2 ^ 64 * 5 ^ 64) := by
        ring
      _ = 2 ^ 11 * (2 * 5) ^ 64 := by 
        rw [show (2 ^ 64 * 5 ^ 64 : ℕ) = (2 * 5) ^ 64 by 
          ring_nf
        ]
      _ = 2 ^ 11 * 10 ^ 64 := by 
        norm_num
  have h9 : (Nat.digits 10 N).sum = 14 := by
    rw [h8]
    native_decide
  exact h9