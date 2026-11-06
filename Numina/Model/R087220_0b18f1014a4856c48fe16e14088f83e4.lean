import Mathlib

theorem algebra_177174 {x y : ℕ} (hy : 0 < y) (hxy : 2^x = 8^(y + 1)) (hxy' : 9^y = 3^(x - 9)) :
    x + y = 27 := by 
  have eq1 : x = 3 * y + 3 := by
    have h1 : 8 ^ (y + 1) = 2 ^ (3 * (y + 1)) := by
      rw [show 8 = 2 ^ 3 by norm_num]
      rw [← pow_mul]
      all_goals omega
    rw [h1] at hxy
    have h3 : x = 3 * (y + 1) := by
      have h4 : (2 : ℕ)^x = 2^(3 * (y + 1)) := hxy
      have h5 : x = 3 * (y + 1) := by
        exact Nat.pow_right_injective (by norm_num) h4
      exact h5
    omega
  
  have eq2 : 2 * y = x - 9 := by
    have h1 : 9 ^ y = 3 ^ (2 * y) := by
      have h2 : 9 ^ y = (3 ^ 2) ^ y := by
        simp [show 9 = 3^2 by norm_num]
      rw [h2]
      rw [← pow_mul]
      all_goals omega
    rw [h1] at hxy'
    have h3 : 2 * y = x - 9 := by
      have h4 : (3 : ℕ) ^ (2 * y) = 3 ^ (x - 9) := hxy'
      have h5 : 2 * y = x - 9 := by
        exact Nat.pow_right_injective (by norm_num) h4
      exact h5
    exact h3
  
  omega