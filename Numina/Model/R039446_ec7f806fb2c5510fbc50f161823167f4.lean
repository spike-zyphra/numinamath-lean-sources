import Mathlib

theorem algebra_14796: IsGreatest {C:ℝ | ∀x y:ℝ, x^2+y^2+1 ≥ C*(x+y)} √2 := by
  constructor
  · -- Show that $\sqrt{2}$ is in the set
    intro x y
    nlinarith [sq_nonneg (x - y), sq_nonneg (x + y - √2), sq_nonneg (x - (√2 / 2)), sq_nonneg (y - (√2 / 2)), Real.sqrt_nonneg 2, Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  · -- Show that $\sqrt{2}$ is greatest in the set
    intro C h
    have h1 := h (√2 / 2) (√2 / 2)
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num), sq_nonneg (C - √2), mul_nonneg (Real.sqrt_nonneg 2) (Real.sqrt_nonneg 2)]