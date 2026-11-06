import Mathlib

theorem algebra_21524 {l w : ℝ} (hl : l = 2 * w) (hw : w > 0)
    (h : l ^ 2 + w ^ 2 = (5 * Real.sqrt 5) ^ 2) : l * w = 50 := by
  have h1 : (5 * Real.sqrt 5) ^ 2 = 125 := by
    calc
      (5 * Real.sqrt 5) ^ 2 = 5^2 * (Real.sqrt 5)^2 := by ring
      _ = 25 * 5 := by norm_num [Real.sq_sqrt]
      _ = 125 := by norm_num
  rw [h1] at h
  rw [hl] at h
  have h2 : 5 * w^2 = 125 := by
    nlinarith
  have hw2 : w^2 = 25 := by
    linarith
  have : l * w = 2 * w^2 := by
    rw [hl]
    ring
  rw [this]
  rw [hw2]
  all_goals norm_num