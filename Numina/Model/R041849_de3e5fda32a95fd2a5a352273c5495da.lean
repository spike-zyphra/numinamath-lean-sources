import Mathlib

theorem algebra_16790  (y : ℝ → ℝ) (hxy : ∃ c, ∀ t, √t * y t = c) (hx2 : y 2 = 4)
    (x : ℝ) (hy1 : y x = 1) : x = 32 := by
  rcases hxy with ⟨c, hc⟩
  have h2 : √(2 : ℝ) * y 2 = c := hc 2
  rw [hx2] at h2
  have hc2 : c = 4 * √(2 : ℝ) := by
    nlinarith 
  have hx_eq : √x * y x = c := hc x
  rw [hy1] at hx_eq
  have h3 : √x = c := by
    nlinarith 
  rw [hc2] at h3
  have h4 : x ≥ 0 := by
    by_contra h
    push_neg at h
    have h5 : √x = 0 := by
      rw [Real.sqrt_eq_zero']
      all_goals linarith 
    rw [h5] at h3
    nlinarith [Real.sqrt_pos.mpr (show (2 : ℝ) > 0 by norm_num : (2 : ℝ) > 0)]
  have h5 : (√x) ^ 2 = (4 * √(2 : ℝ)) ^ 2 := by 
    rw [h3]
  have h6 : (√x) ^ 2 = x := by
    rw [Real.sq_sqrt]
    linarith 
  have h7 : (4 * √(2 : ℝ)) ^ 2 = (32 : ℝ) := by 
    calc 
      (4 * √(2 : ℝ)) ^ 2 = (4 ^ 2) * (√(2 : ℝ) ^ 2) := by ring 
      _ = (16 : ℝ) * (2 : ℝ) := by 
        norm_num [Real.sq_sqrt] 
      _ = (32 : ℝ) := by 
        norm_num 
  rw [h6, h7] at h5 
  nlinarith 
  all_goals linarith 
  all_goals linarith