import Mathlib

theorem algebra_183837 {a : ℝ} (ha : ∃ x y, x ≠ y ∧ x^2 - (15/4)*x + a = 0 ∧ y^2 - (15/4)*y + a = 0 ∧ x = y^2) :
    a = 27/8 ∨ a = -125/8 := by
  rcases ha with ⟨x, y, hxy, hx, hy, hx2⟩
  have h_diff : (x - y) * (x + y - 15 / 4) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h_diff) with
  | inl h =>
    exfalso
    exact hxy (by linarith)
  | inr h_sum =>
    have h_eq1 : x + y = 15 / 4 := by linarith
    have h_eq2 : y^2 + y - 15/4 = 0 := by
      nlinarith [hx2]
    have h_eq3 : 4 * y^2 + 4 * y - 15 = 0 := by
      nlinarith [h_eq2]
    have h_y : (y - 3/2) * (y + 5/2) = 0 := by
      nlinarith [h_eq3]
    cases (mul_eq_zero.mp h_y) with
    | inl h1 =>
      have h5 : y = 3/2 := by linarith
      have h6 : x = 9 / 4 := by
        nlinarith [h5, hx2]
      have ha1 : a = 27 / 8 := by
        nlinarith [hx, h6, h5]
      left
      exact ha1
    | inr h2 =>
      have h7 : y = -5/2 := by linarith
      have h8 : x = 25 / 4 := by
        nlinarith [h7, hx2]
      have ha2 : a = -125 / 8 := by
        nlinarith [hx, h8, h7]
      right
      exact ha2