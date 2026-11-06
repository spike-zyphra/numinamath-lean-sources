import Mathlib

theorem algebra_98015 {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0)
    (h1 : abs x + y = 3) (h2 : abs x * y + x ^ 3 = 0) :
    round (x - y) = -3 := by
  by_cases h : x ≥ 0
  · -- If x ≥ 0, then |x| = x
    have h1' : abs x = x := by 
      rw [abs_of_nonneg h]
    rw [h1'] at h1 h2
    have eq1 : y = 3 - x := by linarith
    rw [eq1] at h2
    have h3 : x * (x ^ 2 - x + 3) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- x = 0
      exfalso 
      apply hx
      linarith 
    · -- x^2 - x + 3 = 0
      have : x ^ 2 - x + 3 > 0 := by 
        nlinarith [sq_nonneg (x - 1 / 2)]
      nlinarith 
  · -- If x < 0, then |x| = -x
    have h1' : abs x = -x := by 
      rw [abs_of_neg (show x < 0 by linarith)]
    rw [h1'] at h1 h2
    have eq1 : y = 3 + x := by linarith
    rw [eq1] at h2
    have h3 : x * (x ^ 2 - x - 3) = 0 := by 
      nlinarith 
    cases' (mul_eq_zero.mp h3) with h4 h5
    · -- x = 0
      nlinarith 
    · -- x^2 - x - 3 = 0
      have h8 : x - y = -3 := by
        nlinarith 
      rw [h8]
      norm_num [round_eq]
      all_goals norm_num
      all_goals norm_num [round_eq]
      all_goals norm_num