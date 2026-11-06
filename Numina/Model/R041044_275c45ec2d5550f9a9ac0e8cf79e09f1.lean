import Mathlib

theorem algebra_305460 {a b c d : ℕ} (h : 27 * (3^a + 3^b + 3^c + 3^d) = 6888) : a + b + c + d = 6 := by 
  have h3 : (27 * (3^a + 3^b + 3^c + 3^d) : ℕ) % 9 = 6888 % 9 := by 
    omega
  norm_num at h3 
  all_goals omega