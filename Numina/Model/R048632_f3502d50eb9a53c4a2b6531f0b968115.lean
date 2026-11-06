import Mathlib

theorem algebra_286218 (n : ℕ) (h : 10^4 * 100^n = 1000^6) : n = 7 := by
  have h1 : 10 ^ 4 * 100 ^ n = 1000 ^ 6 := h
  have eq1 : 100 ^ n = 10 ^ (2 * n : ℕ) := by
    have h2 : 100 ^ n = 10 ^ (2 * n : ℕ) := by
      have h3 : 100 ^ n = (10 ^ 2) ^ n := by
        ring_nf
      rw [h3]
      rw [← pow_mul]
      all_goals ring_nf
    exact h2
  have eq2 : 10 ^ 4 * 100 ^ n = 10 ^ (4 + 2 * n : ℕ) := by
    rw [eq1]
    ring_nf
  have eq3 : 1000 ^ 6 = 10 ^ (18 : ℕ) := by
    norm_num
  rw [eq2, eq3] at h1
  have h2 : 4 + 2 * n = 18 := by
    exact Nat.pow_right_injective (by norm_num) h1
  omega