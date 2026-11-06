import Mathlib

theorem algebra_119443 (a b : ℝ) (h : 3*a^2+3*b^2-2*a-14*b+46/3=0) :
    4/3 ≤ a+b ∧ a+b ≤ 4 := by 
  have h1 : (a - 1/3)^2 + (b - 7/3)^2 = 4/9 := by
    nlinarith
  constructor
  · -- Prove 4/3 ≤ a + b
    nlinarith [sq_nonneg (a - b + 5/3), sq_nonneg (a - 19/9), sq_nonneg (b - 7/9), sq_nonneg ((a + b) - 4), sq_nonneg ((a + b) - 4/3), sq_nonneg ((a - 1/3) - (b - 7/3)), sq_nonneg ((a + b) - (8/3)), sq_nonneg ((b - 7/3) - (a - 1/3))]
  · -- Prove a + b ≤ 4
    nlinarith [sq_nonneg (a - b - 7/3), sq_nonneg (a - 19/9), sq_nonneg (b - 7/9), sq_nonneg ((a + b) - 4/3), sq_nonneg ((a + b) - 4), sq_nonneg ((a - 1/3) - (b - 7/3)), sq_nonneg ((a + b) - (8/3)), sq_nonneg ((b - 7/3) - (a - 1/3))]