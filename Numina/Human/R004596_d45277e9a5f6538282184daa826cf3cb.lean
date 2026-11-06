import Mathlib

theorem algebra_288202 {n : ℕ} (h : 2^200 * 2^203 + 2^163 * 2^241 + 2^126 * 2^277 = 32^n) :
    n = 81 := by
  have h1 : 2^200 * 2^203 + 2^163 * 2^241 + 2^126 * 2^277 = 2^405 := by
    ring
  rw [h1] at h
  have h2 : 2^405 = 2^(5 * n) := by
    rw [h]
    rw [show 32 = 2 ^ 5 by norm_num]
    rw [← pow_mul]
  have h3 : 405 = 5 * n := by
    exact Nat.pow_right_injective (by norm_num) h2
  linarith