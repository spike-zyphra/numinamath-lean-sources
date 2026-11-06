import Mathlib

theorem algebra_306604 (a : ℝ) (h : ∃ x1 x2, x1 ≠ x2 ∧ 3*x1^2-5*x1+a=0 ∧ 3*x2^2-5*x2+a=0 ∧
    x1 > -2 ∧ x1 < 0 ∧ x2 > 1 ∧ x2 < 3) :
    -12 < a ∧ a < 0 := by
  rcases h with ⟨x1, x2, h12, h1, h2, hx11, hx12, hx21, hx22⟩
  -- derive a from h1 and h2
  have h3 : a = -3 * x1^2 + 5 * x1 := by 
    nlinarith
  have h4 : a = -3 * x2^2 + 5 * x2 := by
    nlinarith
  -- solve bounds with nonlinear arithmetic solver
  constructor
  · -- Prove -12 < a
    nlinarith [sq_nonneg (x1 - x2), sq_pos_of_ne_zero (sub_ne_zero_of_ne h12), sq_nonneg (x1 - (-5 / 6)), sq_nonneg (x2 - 2)]
  · -- Prove a < 0
    nlinarith [sq_nonneg (x1 - 5 / 6), sq_nonneg (x1 - 0), sq_nonneg (x2 - 2)]