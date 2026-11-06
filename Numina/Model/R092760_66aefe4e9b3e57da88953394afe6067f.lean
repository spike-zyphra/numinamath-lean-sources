import Mathlib

theorem algebra_14963 {n : ℕ} (h : 4^6 = 8^n) : n = 4 := by
  have h1 : 4^6 = 2^12 := by norm_num
  have h2 : 8^n = 2^(3*n) := by
    rw [show 8 = 2^3 by norm_num]
    rw [pow_mul]
  rw [h1] at h
  rw [h2] at h
  have h3 : 12 = 3 * n := by
    exact Nat.pow_right_injective (by norm_num) h
  have : n = 4 := by 
    omega
  exact this