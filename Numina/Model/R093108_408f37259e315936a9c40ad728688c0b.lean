import Mathlib

theorem algebra_6877 (x y : ℝ) (hx : 0 < x) (hy : 0 < y)
    (h : x^2 - y^2 - 27 = 6 * x + 12 * y) : x - y = 9 := by
  have h1 : (x - 3)^2 - (y + 6)^2 = 0 := by
    nlinarith [h]
  have h2 : (x - 3)^2 = (y + 6)^2 := by linarith
  have h3 : x - 3 = y + 6 ∨ x - 3 = - (y + 6) := by
    apply eq_or_eq_neg_of_sq_eq_sq
    all_goals nlinarith
  cases h3 with
  | inl h4 =>
    linarith
  | inr h5 =>
    nlinarith [show (x + y) > 0 by linarith [hx, hy]]