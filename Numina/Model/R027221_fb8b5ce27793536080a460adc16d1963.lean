import Mathlib

theorem algebra_118775 {x y : ℕ} (hxy : x * 3 = y * 2) (hxy' : x * 4 = y * 5)
    (hdiff : |(x : ℤ) - y| = 28) :
    x ≥ 560 := by 
  have eq1 : x = 0 := by 
    omega
  have eq2 : y = 0 := by
    omega
  rw [show (x : ℤ) = (0 : ℤ) by exact_mod_cast eq1] at hdiff
  rw [show (y : ℤ) = (0 : ℤ) by exact_mod_cast eq2] at hdiff
  norm_num at hdiff
  all_goals 
    omega