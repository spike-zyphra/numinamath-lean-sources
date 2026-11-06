import Mathlib

theorem algebra_111132 {n : ℕ} (hn : n ≠ 0) (x y : ℝ)
    (hx : x = (1 + 1 / n : ℝ)^n) (hy : y = (1 + 1 / n : ℝ)^(n + 1)) :
    y^x = x^y := by 
  rw [hx, hy]
  have h2 : ((1 + (1 / n) : ℝ) ^ (n + 1 : ℕ)) ^ ((1 + (1 / n) : ℝ) ^ n) = (1 + (1 / n) : ℝ) ^ ((n + 1 : ℝ) * ((1 + (1 / n) : ℝ) ^ n)) := by 
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_cast
    all_goals 
      have hn1 : (n : ℝ) > 0 := by positivity
      positivity 
  have h3 : ((1 + (1 / n) : ℝ) ^ n) ^ ((1 + (1 / n) : ℝ) ^ (n + 1 : ℕ)) = (1 + (1 / n) : ℝ) ^ ((n : ℝ) * ((1 + (1 / n) : ℝ) ^ (n + 1 : ℕ)) ) := by 
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_cast
    all_goals 
      have hn1 : (n : ℝ) > 0 := by positivity
      positivity 
  have h4 : (n + 1 : ℝ) * ((1 + (1 / n) : ℝ) ^ n) = (n : ℝ) * ((1 + (1 / n) : ℝ) ^ (n + 1 : ℕ)) := by 
    have eq1 : ( (1 + (1 / n) : ℝ) ^ (n + 1 : ℕ) ) = ( (1 + (1 / n) : ℝ) ^ n ) * ( (1 + (1 / n) : ℝ) ) := by 
      simp [pow_succ] 
    rw [eq1] 
    field_simp at *
    <;> ring_nf
  rw [h2, h3] 
  rw [h4] 
  all_goals 
    norm_num