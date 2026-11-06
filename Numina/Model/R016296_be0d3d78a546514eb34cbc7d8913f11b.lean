import Mathlib

theorem algebra_179207 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a + b^2 + c^2 = b + a^2 + c^2 ∧ a + b^2 + c^2 = c + a^2 + b^2) :
    a = b ∨ b = c ∨ a = c := by
  rcases h with ⟨h1, h2⟩
  have eq1 : (b - a) * (b + a - 1) = 0 := by
    nlinarith
  have eq2 : (c - a) * (c + a - 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp eq1) with
  | inl h3 =>
    left
    linarith
  | inr h3 =>
    cases (mul_eq_zero.mp eq2) with
    | inl h4 =>
      right
      right
      linarith
    | inr h4 =>
      have h5 : b + a = 1 := by linarith
      have h6 : c + a = 1 := by linarith
      have eq3 : b = c := by linarith
      right
      left
      linarith