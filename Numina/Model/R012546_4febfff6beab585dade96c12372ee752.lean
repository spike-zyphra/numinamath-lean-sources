import Mathlib

theorem algebra_195388 (c : ℝ) (hc : c > 0 ∧ c ≠ 1) (h : Real.logb c 27 = 0.75) :
    c = 81 := by
  have h1 : c ^ (0.75 : ℝ) = 27 := by
    rw [←h]
    field_simp [Real.rpow_logb, hc.1, hc.2]
  have h3 : c = (27 : ℝ) ^ (4 / 3 : ℝ) := by
    have h4 : c ^ (0.75 : ℝ) = 27 := h1
    have h5 : c = (c ^ (0.75 : ℝ)) ^ (4 / 3 : ℝ) := by
      rw [← Real.rpow_mul]
      norm_num
      all_goals linarith [hc.1]
    rw [show (c ^ (0.75 : ℝ) ) = (27 : ℝ) by linarith [h1] ] at h5
    linarith
  have h6 : (27 : ℝ) ^ (4 / 3 : ℝ) = 81 := by
    have h7 : (27 : ℝ) ^ (4 / 3 : ℝ) = ((3 : ℝ) ^ (3 : ℝ)) ^ (4 / 3 : ℝ) := by
      norm_num
    rw [h7]
    have h8 : ((3 : ℝ) ^ (3 : ℝ)) ^ (4 / 3 : ℝ) = (3 : ℝ) ^ (4 : ℝ) := by
      rw [← Real.rpow_mul]
      ring_nf
      all_goals norm_num
    rw [h8]
    norm_num
  rw [h6] at h3
  linarith