import Mathlib

theorem algebra_19154 (k : ℕ) (h : (3 ^ k) ^ 6 = 3 ^ 6) : k = 1 := by 
  have h1 : (3 ^ k) ^ 6 = 3 ^ (k * 6) := by 
    rw [Nat.pow_mul]
  rw [h1] at h 
  have h2 : k * 6 = 6 := by 
    exact Nat.pow_right_injective (by norm_num) h 
  have : k = 1 := by 
    omega 
  exact this