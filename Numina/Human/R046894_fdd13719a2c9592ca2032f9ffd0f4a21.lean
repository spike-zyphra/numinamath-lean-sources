import Mathlib

theorem calculus_15004 : crossProduct ![2, 0, 3] ![5, -1, 7] = ![3, 1, -2] := by
  simp [crossProduct]
  <;> norm_num