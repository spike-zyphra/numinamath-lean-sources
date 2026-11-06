import Mathlib

open Real

theorem other_176373 (h : 48 * 2 * π * (6370 + 200) = 1982000) :
    (1982000 / (48 * 2 * π * (6370 + 200))) = 7.77 := by 
  have h1 : (48 * 2 * π * (6370 + 200) ) ≠ (1982000 : ℝ) := by 
    nlinarith [Real.pi_gt_three, Real.pi_lt_31416]
  contradiction