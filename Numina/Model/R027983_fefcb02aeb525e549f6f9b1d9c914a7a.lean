import Mathlib

theorem number_theory_243455 : max (max (max (max (2^5000 : ℕ) (3^4000)) (4^3000)) (5^2000)) (6^1000) = 3^4000 := by
  have h1 : (2^5000 : ℕ) ≤ 3^4000 := by
    norm_num
  have h2 : (4^3000 : ℕ) ≤ 3^4000 := by 
    norm_num
  have h3 : (5^2000 : ℕ) ≤ 3^4000 := by 
    norm_num
  have h4 : (6^1000 : ℕ) ≤ 3^4000 := by
    norm_num
  simp [max_eq_right, max_eq_left, h1, h2, h3, h4]
  all_goals 
    omega