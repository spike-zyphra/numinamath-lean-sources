import Mathlib

theorem algebra_260264 (d t : ℝ) (ht : t > 0) (h : d / t = 3 * d / (5 * t) + 2) (h' : d / t + 50 / 5 = d / (t + 40 / 60)) :
    d = 200 := by
  have ht1 : t ≠ 0 := by linarith
  have ht2 : t + (40 / 60) ≠ 0 := by
    nlinarith
  have eq1 : 5 * d = 3 * d + 10 * t := by
    have : d / t = 3 * d / (5 * t) + 2 := h
    have ht3 : 5 * t ≠ 0 := by
      intro h1
      apply ht1
      linarith
    field_simp [ht1, ht3] at this ⊢
    nlinarith
  -- Subtract 3 * d from both sides to get 2 * d = 10 * t
  have eq2 : d = 5 * t := by
    linarith
  have ht2' : t + 40 / 60 > 0 := by
    nlinarith [ht]
  -- Creating equation from h'
  have eq4 : (d / t + 50 / 5) = (d / (t + 40 / 60)) := by
    linarith [h']
  have eq5 : 40 / 60 = (2 / 3) := by norm_num
  have ht3' : t + (40 / 60) = t + (2 / 3) := by
    linarith [eq5]
  rw [show 50 / 5 = (10 : ℝ) by norm_num] at eq4
  have eq7 : 40 / 60 = (2 / 3 : ℝ) := by norm_num
  rw [eq7] at eq4
  have eq8 : t + (2 / 3 : ℝ) > 0 := by
    nlinarith [ht]
  have ht9 : t + (2 / 3 : ℝ) ≠ 0 := by
    linarith [eq8]
  rw [eq2] at eq4
  field_simp [ht1, ht9] at eq4 ⊢
  nlinarith [sq_pos_of_pos ht, sq_pos_of_pos eq8, sq_pos_of_pos (show 0 < (1 : ℝ) by norm_num), sq_nonneg (t - (1 : ℝ)), sq_nonneg (d - (200 : ℝ)), sq_nonneg (t + (1 : ℝ))]