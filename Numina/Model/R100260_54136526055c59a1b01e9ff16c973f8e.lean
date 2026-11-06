import Mathlib

open Real

theorem algebra_8557 (x : ℝ) :
    x ^ 2 - 9 * x - 10 > 0 ∧ 2023 > 0 ∧ 2023 ≠ 1 → x < -1 ∨ x > 10 := by
  intro h
  have h1 : x^2 - 9 * x - 10 > 0 := h.1
  -- Factor the quadratic
  have h2 : (x - 10) * (x + 1) > 0 := by nlinarith
  -- Apply the product sign rule
  cases (mul_pos_iff.mp h2) with
  | inl h3 =>
    -- Case where both factors are positive, so x - 10 > 0 and x + 1 > 0, implying x > 10
    right
    linarith
  | inr h4 =>
    -- Case where both factors are negative, so x - 10 < 0 and x + 1 < 0, implying x < -1
    left
    linarith