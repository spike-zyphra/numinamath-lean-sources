import Mathlib

theorem algebra_17199 {x : ℝ} (h : 25 * x = 6) :
    600 * x = 144 := by
  have hx : x = (6 : ℝ) / 25 := by
    linarith
  rw [hx]
  norm_num