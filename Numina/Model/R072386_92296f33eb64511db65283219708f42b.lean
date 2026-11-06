import Mathlib

theorem algebra_16015 (x1 x2 : ℝ) (hx1 : x1^2 + 30 * x1 + 180 = -36) (hx2 : x2^2 + 30 * x2 + 180 = -36)
    (hroots : x1 ≠ x2) :
    |x1 - x2| = 6 := by
  have h1 : x1^2 + 30 * x1 + 216 = 0 := by linarith
  have h2 : x2^2 + 30 * x2 + 216 = 0 := by linarith
  have factored1 : (x1 + 12) * (x1 + 18) = 0 := by
    nlinarith
  have factored2 : (x2 + 12) * (x2 + 18) = 0 := by
    nlinarith
  have root1 : x1 = -12 ∨ x1 = -18 := by
    cases (mul_eq_zero.mp factored1) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  have root2 : x2 = -12 ∨ x2 = -18 := by
    cases (mul_eq_zero.mp factored2) with
    | inl h =>
      left
      linarith
    | inr h =>
      right
      linarith
  cases root1 with
  | inl h11 =>
    cases root2 with
    | inl h21 =>
      exfalso
      exact hroots (by linarith)
    | inr h22 =>
      rw [h11, h22]
      norm_num [abs_of_pos]
  | inr h12 =>
    cases root2 with
    | inl h21 =>
      rw [h12, h21]
      norm_num [abs_of_pos]
    | inr h22 =>
      exfalso
      exact hroots (by linarith)