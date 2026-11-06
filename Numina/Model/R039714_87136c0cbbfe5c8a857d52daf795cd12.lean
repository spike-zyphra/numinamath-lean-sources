import Mathlib

theorem algebra_175208 (n : ℕ) : (9^n + 9^n + 9^n = 3^2007) ↔ n = 1003 := by
  constructor
  · -- Assume 9^n + 9^n + 9^n = 3^2007, prove n = 1003
    intro h
    have eq1 : 9^n + 9^n + 9^n = 3 * (9^n) := by
      ring
    rw [eq1] at h
    have eq2 : 9^n = 3 ^ (2 * n) := by
      rw [show 9 = 3 ^ 2 by norm_num]
      rw [← pow_mul]
    rw [eq2] at h
    have eq3 : 3 * (3 ^ (2 * n)) = 3 ^ (2 * n + 1) := by
      ring_nf
    rw [eq3] at h
    have eq4 : 2 * n + 1 = 2007 := by
      have h1 : 3 ^ (2 * n + 1) = 3 ^ 2007 := by
        exact h
      exact Nat.pow_right_injective (by norm_num) h1
    have eq5 : 2 * n = 2006 := by
      omega
    have eq6 : n = 1003 := by
      omega
    exact eq6
  · -- Assume n = 1003, prove 9^n + 9^n + 9^n = 3^2007
    intro h
    rw [h]
    have eq1 : 9 ^ 1003 + 9 ^ 1003 + 9 ^ 1003 = 3 * (9 ^ 1003) := by
      ring
    have eq2 : 9 ^ 1003 = 3 ^ (2 * 1003) := by
      rw [show 9 = 3 ^ 2 by norm_num]
      rw [← pow_mul]
    have eq3 : 3 * (9 ^ 1003) = 3 ^ 2007 := by
      rw [eq2]
      norm_num
    rw [eq1]
    exact eq3