import Mathlib

theorem algebra_335 {x : ℝ} (hx : x ≥ 0) :
    (Real.sqrt x)^3 * (x ^ (1 / 3 : ℝ))^2 = x^(13 / 6 : ℝ) := by
  have h1 : Real.sqrt x = x ^ (1 / 2 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
  have h2 : (Real.sqrt x) ^ 3 = x ^ (3 / 2 : ℝ) := by 
    rw [h1]
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h3 : (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ (2 / 3 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  by_cases h : x = 0 
  · -- Case where x = 0
    rw [h]
    norm_num
  · -- Case where x ≠ 0 
    have hx2 : x > 0 := by 
      by_contra h'
      push_neg at h'
      have h3x : x = 0 := by linarith 
      contradiction 
    have eq1 : (Real.sqrt x) ^ 3 * (x ^ (1 / 3 : ℝ)) ^ 2 = x ^ (3 / 2 : ℝ) * x ^ (2 / 3 : ℝ) := by 
      rw [h2, h3] 
    have eq2 : x ^ (3 / 2 : ℝ) * x ^ (2 / 3 : ℝ) = x ^ (13 / 6 : ℝ) := by 
      have h4 : x ^ (3 / 2 : ℝ) * x ^ (2 / 3 : ℝ) = x ^ ((3 / 2 : ℝ) + (2 / 3 : ℝ)) := by 
        rw [← Real.rpow_add]
        ring_nf 
        all_goals 
          linarith [hx2] 
      rw [h4] 
      norm_num 
    rw [eq1, eq2]