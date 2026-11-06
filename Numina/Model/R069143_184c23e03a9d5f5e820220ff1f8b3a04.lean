import Mathlib

theorem algebra_20522 {N : ℕ} (h : (2^3)^(2^3) = 2^N) : N=24 := by
  have h1 : (2^3)^(2^3) = 2^24 := by
    norm_num
  rw [h1] at h
  have h2 : 24 = N := by
    exact Nat.pow_right_injective (by norm_num) h
  linarith