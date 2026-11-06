import Mathlib

open Real

theorem inequalities_231376 :
    3.14 < Real.pi ∧ Real.pi < 3.142 ∧ 9.86 < (Real.pi ^ 2) ∧ (Real.pi ^ 2) < 9.87 := by 
  have h1 : 3.14 < Real.pi := by
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h2 : Real.pi < 3.142 := by
    linarith [Real.pi_gt_31415, Real.pi_lt_31416]
  have h3 : 9.86 < Real.pi ^ 2 := by
    nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, 
      sq_nonneg (Real.pi - 3.1415), sq_nonneg (Real.pi - 3.1416)]
  have h4 : Real.pi ^ 2 < 9.87 := by
    nlinarith [Real.pi_gt_31415, Real.pi_lt_31416, 
      sq_nonneg (Real.pi - 3.1415), sq_nonneg (Real.pi - 3.1416)]
  constructor
  · exact h1
  constructor
  · exact h2
  constructor
  · exact h3
  · exact h4