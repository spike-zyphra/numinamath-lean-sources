import Mathlib

theorem algebra_21595 {B h V : ℝ} (hB : B = 30) (hV : V = B * h / 3) (h : h = 6.5) :
    V = 65 := by
  rw [hB] at hV
  rw [h] at hV
  rw [hV]
  norm_num