import Mathlib

open Real

theorem algebra_116533 {a b : ℝ} (ha : a = 1 / 2) (h : (a + 1) * (b + 1) = 2) :
    arctan a + arctan b = π / 4 := by
  have hb : b = 1/3 := by
    rw [ha] at h
    linarith
  rw [ha, hb]
  have h1 : arctan (1 / 2 : ℝ) + arctan (1 / 3 : ℝ) = π / 4 := by
    have h2 : arctan (1 / 2 : ℝ) + arctan (1 / 3 : ℝ) = arctan (1 : ℝ) := by
      rw [arctan_add]
      norm_num
      all_goals norm_num
    have h3 : arctan (1 : ℝ) = π / 4 := Real.arctan_one
    rw [h3] at h2
    linarith [h2]
  linarith [h1]