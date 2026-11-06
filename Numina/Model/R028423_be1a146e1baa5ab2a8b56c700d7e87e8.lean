import Mathlib

theorem algebra_166421 {x y : ℝ} (hx : x ≥ 0) (hy : y ≥ 0)
    (h1 : (x ^ ((1 : ℝ) / 4) + y ^ ((1 : ℝ) / 4)) = 3) (h2 : x + y = 17) :
    (x, y) = (1, 16) ∨ (x, y) = (16, 1) := by
  have h3 : (x ^ ((1 : ℝ) / 4)) ^ 4 = x := by 
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num
    all_goals linarith 
  have h4 : (y ^ ((1 : ℝ) / 4)) ^ 4 = y := by 
    rw [← Real.rpow_natCast]
    rw [← Real.rpow_mul]
    norm_num 
    all_goals linarith 
  have eq1 : (x ^ ((1 : ℝ) / 4)) ^ 4 + (y ^ ((1 : ℝ) / 4)) ^ 4 = 17 := by
    nlinarith [h2, h3, h4] 
  have eq2 : x ^ ((1 : ℝ) / 4) + y ^ ((1 : ℝ) / 4) = 3 := h1 
  have h5 : (x ^ ((1 : ℝ) / 4) - 1) * (x ^ ((1 : ℝ) / 4) - 2) = 0 := by
    have eq3 : (y ^ ((1 : ℝ) / 4)) = 3 - (x ^ ((1 : ℝ) / 4)) := by 
      linarith 
    rw [eq3] at eq1
    nlinarith [sq_nonneg ((x ^ ((1 : ℝ) / 4)) ^ 2 - (x ^ ((1 : ℝ) / 4) ) * 3 + 4), sq_nonneg ((x ^ ((1 : ℝ) / 4)) - 1), sq_nonneg ((x ^ ((1 : ℝ) / 4)) - 2), sq_nonneg ((x ^ ((1 : ℝ) / 4)) ^ 2 - 4)]
  cases' (mul_eq_zero.mp h5) with h6 h7 
  · -- Assume h6: (x ^ (1 / 4 : ℝ)) - 1 = 0, so x ^ (1 / 4 : ℝ) = 1 
    have hx1 : x ^ ((1 : ℝ) / 4) = 1 := by linarith 
    have hy16 : y ^ ((1 : ℝ) / 4) = 2 := by 
      nlinarith [h1, hx1] 
    have hx0 : x = 1 := by 
      have h8 : x ^ ((1 : ℝ) / 4) = 1 := hx1 
      rw [← h3] at h8 
      nlinarith [h8] 
    have hy16' : y = 16 := by 
      have h9 : y ^ ((1 : ℝ) / 4) = 2 := hy16 
      rw [← h4] at h9 
      nlinarith [h9] 
    left 
    simp [hx0, hy16']
  · -- Assume h7: (x ^ (1 / 4 : ℝ)) - 2 = 0, so x ^ (1 / 4 : ℝ) = 2 
    have hx16 : x ^ ((1 : ℝ) / 4) = 2 := by linarith 
    have hy1 : y ^ ((1 : ℝ) / 4) = 1 := by 
      nlinarith [h1, hx16] 
    have hx16' : x = 16 := by 
      have h8 : x ^ ((1 : ℝ) / 4) = 2 := hx16 
      rw [← h3] at h8 
      nlinarith [h8] 
    have hy0 : y = 1 := by 
      have h9 : y ^ ((1 : ℝ) / 4) = 1 := hy1 
      rw [← h4] at h9 
      nlinarith [h9] 
    right 
    simp [hx16', hy0]