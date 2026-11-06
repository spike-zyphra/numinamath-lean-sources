import Mathlib

theorem algebra_153406 : (2 : ℝ)^(-3 : ℝ) = 1 / 8 ∧ ((1 / 3) : ℝ)^(-2 : ℝ) = 9 ∧ ((2 / 3) : ℝ)^(-4 : ℝ) = 81 / 16 ∧ (-0.2 : ℝ)^(-3 : ℝ) = -125 := by 
  constructor
  · -- Proof for (2 : ℝ)^(-3 : ℝ) = 1 / 8
    norm_num
  constructor
  · -- Proof for ((1 / 3) : ℝ)^(-2 : ℝ) = 9
    norm_num
  constructor
  · -- Proof for ((2 / 3) : ℝ)^(-4 : ℝ) = 81 / 16
    norm_num
  · -- Proof for (-0.2 : ℝ)^(-3 : ℝ) = -125
    norm_num