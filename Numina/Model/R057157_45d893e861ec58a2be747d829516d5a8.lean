import Mathlib

theorem calculus_22494 : crossProduct ![1, -1, 2] ![3, 4, -5] = ![ -3, 11, 7] := by
  funext i
  fin_cases i <;> simp [crossProduct] <;> norm_num