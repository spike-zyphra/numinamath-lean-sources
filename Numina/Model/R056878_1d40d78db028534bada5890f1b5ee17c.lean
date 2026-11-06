import Mathlib

open Real

theorem inequalities_603711 (x y : ℝ) (hy : 0 ≤ y) (h : y * (y + 1) ≤ (x + 1)^2) :
    y * (y - 1) ≤ x^2 := by 
  nlinarith [sq_nonneg (x + 1 - y), sq_nonneg (x - y), h, sq_nonneg (x - (y - 1)), sq_nonneg (x + 1 - (y + 1)), sq_nonneg (x - y)]