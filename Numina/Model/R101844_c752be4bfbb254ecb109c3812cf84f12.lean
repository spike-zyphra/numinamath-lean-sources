import Mathlib

theorem algebra_145370 (d D : ℝ) (hd : d = 75) (hD : D = d - 0.5)
    (α : ℝ) (hα : α = 0.000012) :
    D = 74.5 := by
  rw [hD, hd]
  norm_num