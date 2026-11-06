import Mathlib

theorem algebra_256326 (x : ℕ) (h : 2 * 2 ^ (2 * x) = 4 ^ x + 64) : x = 3 := by
  have eq1 : 4 ^ x = 2 ^ (2 * x) := by
    rw [show 4 ^ x = (2 ^ 2) ^ x by ring]
    rw [pow_mul]
    all_goals ring_nf
  rw [eq1] at h
  have eq2 : (2 : ℕ) ^ (2 * x) = 64 := by
    omega
  have eq3 : 2 * x = 6 := by
    have h1 : (2 : ℕ) ^ (2 * x) = 64 := eq2
    have h3 : (2 * x : ℕ) = 6 := by
      have h4 : (2 : ℕ) ^ (2 * x) = (2 : ℕ) ^ (6 : ℕ) := by
        rw [h1]
        all_goals norm_num
      have h5 : (2 * x : ℕ) = (6 : ℕ) := by
        exact Nat.pow_right_injective (by norm_num) h4
      omega
    omega
  have eq4 : x = 3 := by
    omega
  exact eq4