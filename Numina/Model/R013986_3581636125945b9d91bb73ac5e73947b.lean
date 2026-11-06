import Mathlib

theorem algebra_323352 (a : ℝ) (ha : a > 0) :
    (∃ x1 x2 x3 : ℝ, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
      x1^2 + (x1^2 - a)^2 = a^2 ∧
      x2^2 + (x2^2 - a)^2 = a^2 ∧
      x3^2 + (x3^2 - a)^2 = a^2) ↔ a > 1 / 2 := by
  constructor
  intro h
  rcases h with ⟨x1, x2, x3, h1, h2, h3, h4, h5, h6⟩
  have eq1 : x1^2 * (x1^2 + 1 - 2 * a) = 0 := by
    nlinarith
  have eq2 : x2^2 * (x2^2 + 1 - 2 * a) = 0 := by
    nlinarith
  have eq3 : x3^2 * (x3^2 + 1 - 2 * a) = 0 := by
    nlinarith
  by_contra h'
  push_neg at h'
  have h7 : a ≤ 1 / 2 := by linarith
  have eq1' : x1^2 = 0 := by
    nlinarith [sq_nonneg (x1^2), sq_nonneg (x1^2 - (2 * a - 1)), sq_nonneg (a - 1 / 2) ]
  have eq2' : x2^2 = 0 := by
    nlinarith [sq_nonneg (x2^2), sq_nonneg (x2^2 - (2 * a - 1)), sq_nonneg (a - 1 / 2) ]
  have eq3' : x3^2 = 0 := by
    nlinarith [sq_nonneg (x3^2), sq_nonneg (x3^2 - (2 * a - 1)), sq_nonneg (a - 1 / 2) ]
  have hx1 : x1 = 0 := by
    nlinarith
  have hx2 : x2 = 0 := by
    nlinarith
  have hx3 : x3 = 0 := by
    nlinarith
  exfalso
  exact h1 (by linarith)
  intro h
  have ha1 : a > 1 / 2 := by linarith
  have h8 : 2 * a - 1 > 0 := by linarith
  use Real.sqrt (2 * a - 1)
  use -Real.sqrt (2 * a - 1)
  use (0 : ℝ)
  constructor
  · -- Show x1 ≠ x2
    have h9 : Real.sqrt (2 * a - 1) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    nlinarith
  constructor
  · -- Show x2 ≠ x3
    have h9 : Real.sqrt (2 * a - 1) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    nlinarith [Real.sqrt_nonneg (2 * a - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * a - 1 by linarith)]
  constructor
  · -- Show x3 ≠ x1
    have h9 : Real.sqrt (2 * a - 1) > 0 := by
      apply Real.sqrt_pos.mpr
      linarith
    nlinarith [Real.sqrt_nonneg (2 * a - 1), Real.sq_sqrt (show (0 : ℝ) ≤ 2 * a - 1 by linarith)]
  constructor
  · -- Show x1^2 + (x1^2 - a)^2 = a^2
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * a - 1 by linarith)]
  constructor
  · -- Show x2^2 + (x2^2 - a)^2 = a^2
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 * a - 1 by linarith)]
  · -- Show x3^2 + (x3^2 - a)^2 = a^2
    nlinarith