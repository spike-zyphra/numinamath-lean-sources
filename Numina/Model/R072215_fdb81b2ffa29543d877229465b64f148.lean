import Mathlib

theorem algebra_268606 (h : (Real.pi * (1 / 2)^2) * 100 = 10000) :
    |(Real.pi * (1 + 10 / 100)^2) * 100 - 10000| = 4 := by
  have h1 : Real.pi < 3.15 := by
    linarith [Real.pi_lt_315]
  nlinarith [Real.pi_gt_three]