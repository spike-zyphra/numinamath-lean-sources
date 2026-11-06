import Mathlib

theorem algebra_18849 (n : ℕ) : (9 : ℕ)^(18*n) = 27^24 ↔ n = 2 := by 
  constructor
  · -- Assume (9 : ℕ)^(18*n) = 27^24, prove n = 2
    intro h
    have h1 : (9 : ℕ) ^ (18 * n) = 3 ^ (36 * n) := by
      rw [show 9 = 3 ^ 2 by norm_num]
      rw [← pow_mul]
      ring_nf
    have h2 : (27 : ℕ) ^ 24 = 3 ^ 72 := by
      norm_num
    rw [h1] at h 
    rw [h2] at h
    have h3 : 36 * n = 72 := by 
      exact Nat.pow_right_injective (by norm_num) h
    have hn : n = 2 := by 
      omega
    exact hn
  · -- Assume n = 2, prove (9 : ℕ)^(18*n) = 27^24
    intro h
    rw [h]
    norm_num