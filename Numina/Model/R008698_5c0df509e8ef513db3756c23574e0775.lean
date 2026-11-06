import Mathlib
open Real

theorem algebra_9140 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x) (hfpos : ∀ x > 0, f x = (3 ^ x - 4) / 3 ^ x) :
    f (f (logb 3 2)) = 1 / 3 := by

  have h1 : logb 3 2 > 0 := by
    apply logb_pos
    all_goals norm_num
  
  have h2 : f (logb 3 2) = -1 := by
    specialize hfpos (logb 3 2) h1
    have h3 : (3 : ℝ) ^ (logb 3 2) = (2 : ℝ) := by
      rw [Real.rpow_logb]
      all_goals norm_num
    rw [hfpos]
    rw [h3]
    norm_num

  have h4 : f (1 : ℝ) = -1 / 3 := by
    specialize hfpos (1 : ℝ) (by norm_num)
    rw [hfpos]
    norm_num

  have h5 : f (- (1 : ℝ)) = 1 / 3 := by
    have h6 : f (- (1 : ℝ)) = - f (1 : ℝ) := hodd (1 : ℝ)
    rw [h6]
    rw [h4]
    all_goals norm_num
  
  rw [h2]
  exact h5