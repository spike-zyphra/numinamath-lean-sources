import Mathlib

theorem algebra_285638 (total : ℝ) (h : total = 100) (gold : ℝ) (h1 : gold = 30) (h2 : gold + (1 / 5) * (total - gold) = total) :
    gold = 50 := by
  rw [h] at h2
  rw [h1] at h2
  linarith