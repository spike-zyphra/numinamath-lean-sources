import Mathlib
open Real

theorem algebra_6624 {x : ℝ} : (0.5 : ℝ)^x = 128^2000 ↔ x = -14000 := by
  constructor
  · -- Forward direction: assume (0.5 : ℝ)^x = 128^2000, prove x = -14000
    intro h_eq
    have h1 : (0.5 : ℝ) ^ x = (2 : ℝ) ^ (-x : ℝ) := by
      have h : (0.5 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      rw [h]
      rw [← Real.rpow_mul]
      ring_nf
      all_goals linarith
    have h2 : (2 : ℝ) ^ (-x : ℝ) = (2 : ℝ) ^ (14000 : ℝ) := by
      rw [← h1]
      norm_num at h_eq ⊢
      linarith
    have h3 : -x = (14000 : ℝ) := by
      apply_fun (Real.logb (2 : ℝ)) at h2
      simp at h2 ⊢
      linarith
    have hx : x = -14000 := by linarith
    exact hx
  · -- Backward direction: assume x = -14000, prove (0.5 : ℝ)^x = 128^2000
    intro h_eq
    rw [h_eq]
    have h1 : (0.5 : ℝ) ^ (-14000 : ℝ) = (2 : ℝ) ^ (14000 : ℝ) := by
      have h : (0.5 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by norm_num
      rw [h]
      rw [← Real.rpow_mul]
      norm_num
      all_goals norm_num
    have h2 : (128 : ℝ) ^ 2000 = (2 : ℝ) ^ (14000 : ℝ) := by
      norm_num
    rw [h1]
    linarith [h2]