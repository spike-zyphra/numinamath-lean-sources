import Mathlib

open Real

theorem inequalities_2236 : (-(1999/2000 : ℝ) < -(1998/1999 : ℝ)) ∧ (-(1998/1999 : ℝ) < -(999/1000 : ℝ)) ∧ (-(999/1000 : ℝ) < -(998/999 : ℝ)) := by
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num