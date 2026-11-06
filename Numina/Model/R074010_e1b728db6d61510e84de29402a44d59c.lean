import Mathlib

open Matrix Finset

theorem calculus_22570 (v w : Fin 3 → ℝ)
    (h : crossProduct v w = ![2, 7, -13]) :
    crossProduct w v = ![ -2, -7, 13] := by
  have h1 : crossProduct w v = - crossProduct v w := by
    simp [crossProduct]
    all_goals ring_nf
  rw [h1, h]
  all_goals norm_num
  all_goals ring_nf