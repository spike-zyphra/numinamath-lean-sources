import Mathlib

theorem algebra_98021 (x y : ℝ) (h : 3 * x + 5 * y = 15) (h1 : x ≠ 0) (h2 : y ≠ 0)
    (h3 : abs x = abs y) :
    (x > 0 ∧ y > 0) ∨ (x < 0 ∧ y > 0) := by
  cases abs_eq_abs.1 h3 with
  | inl h4 =>
    have h5 : y = x := by linarith
    have hx : x = 15 / 8 := by
      linarith [h, h5]
    left
    constructor
    · linarith [hx]
    · linarith [hx, h5]
  | inr h6 =>
    have h7 : y = -x := by linarith
    have hx : x = -15 / 2 := by
      linarith [h, h7]
    right
    constructor
    · linarith [hx]
    · linarith [hx, h7]