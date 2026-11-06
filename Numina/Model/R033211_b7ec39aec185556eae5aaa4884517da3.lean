import Mathlib

theorem algebra_278903 {a b c : ℝ} :
    a*(a-c)^2+b*(b-c)^2-(a-c)*(b-c)*(a+b-c) =
    b*(b-a)^2+c*(c-a)^2-(b-a)*(c-a)*(b+c-a) ∧
    b*(b-a)^2+c*(c-a)^2-(b-a)*(c-a)*(b+c-a) =
    c*(c-b)^2+a*(a-b)^2-(c-b)*(a-b)*(c+a-b) := by 
  constructor
  · -- Prove the first equality
    ring
  · -- Prove the second equality
    ring