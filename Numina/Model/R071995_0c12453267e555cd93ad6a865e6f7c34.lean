import Mathlib

theorem algebra_210498 {e f : ℝ → ℝ} (he : e 1 = 1) (hf : f (-1) = 1)
    (h : |(deriv e 1) - (deriv f (-1))| = 2) :
    ∃ x y, x^2 * 2 - x^2 = y^2 ∧ (x ≠ 1 ∨ y ≠ 1) ∧ (x ≠ -1 ∨ y ≠ 1) := by
  use 0, 0
  constructor
  · norm_num
  constructor
  · norm_num
  · norm_num