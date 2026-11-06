import Mathlib

theorem algebra_170084 {x : ℝ} (hx : x > 0) (h : x ^ ((1 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2) = 8) :
    (x ^ 2 + 1) / x = 62 := by
  have h1 : x ^ ((1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2) = 1 := by
    have h2 : x ^ ((1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2) = x ^ ((1 : ℝ) / 2 + (-(1 : ℝ) / 2)) := by 
      rw [← Real.rpow_add]
      ring_nf
      all_goals linarith
    have h3 : (1 : ℝ) / 2 + (-(1 : ℝ) / 2) = (0 : ℝ) := by ring_nf
    rw [h3] at h2
    rw [h2]
    norm_num
  have h2 : (x ^ ((1 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2)) ^ 2 = 64 := by 
    rw [h]
    norm_num
  have h3 : (x ^ ((1 : ℝ) / 2) + x ^ (-(1 : ℝ) / 2)) ^ 2 = 
      (x ^ ((1 : ℝ) / 2)) ^ 2 + (x ^ (-(1 : ℝ) / 2)) ^ 2 + 2 * (x ^ ((1 : ℝ) / 2) * x ^ (-(1 : ℝ) / 2)) := by 
    ring
  rw [h3] at h2
  rw [h1] at h2
  have h4 : (x ^ ((1 : ℝ) / 2)) ^ 2 = x := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    norm_num
    all_goals linarith
  have h5 : (x ^ (-(1 : ℝ) / 2)) ^ 2 = x ^ (-1 : ℝ) := by 
    rw [← Real.rpow_natCast, ← Real.rpow_mul]
    ring_nf
    all_goals linarith
  rw [h4, h5] at h2
  have h6 : x ^ (-1 : ℝ) = 1 / x := by 
    simp [Real.rpow_neg_one]
  rw [h6] at h2
  have h7 : x + 1 / x = 62 := by 
    field_simp at h2 ⊢
    nlinarith
  have h8 : (x ^ 2 + 1) / x = x + 1 / x := by 
    field_simp
    <;> ring
  rw [h8, h7]