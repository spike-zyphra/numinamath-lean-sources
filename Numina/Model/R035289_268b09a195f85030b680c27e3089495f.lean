import Mathlib

theorem algebra_232326 (a b c : ℝ) (ha : a ≠ 0) (hroots : ∃ x1 x2 x3, x1 ≠ x2 ∧ x2 ≠ x3 ∧ x3 ≠ x1 ∧
    a * x1^2 + b * x1 + c = 0 ∧ a * x2^2 + b * x2 + c = 0 ∧ a * x3^2 + b * x3 + c = 0)
    (hcircle : ∃ x4, x4 ≠ x1 ∧ x4 ≠ x2 ∧ x4 ≠ x3 ∧ a * x4^2 + b * x4 + c = 0) :
    c = 1 / 4 := by
  rcases hroots with ⟨x1, x2, x3, hx12, hx23, hx31, h1, h2, h3⟩
  have eq1 : a * x1^2 + b * x1 + c = 0 := h1
  have eq2 : a * x2^2 + b * x2 + c = 0 := h2
  have eq3 : a * x3^2 + b * x3 + c = 0 := h3
  have eq12 : a * (x1^2 - x2^2) + b * (x1 - x2) = 0 := by
    nlinarith
  have eq13 : a * (x1^2 - x3^2) + b * (x1 - x3) = 0 := by
    nlinarith
  have hx12ne : x1 - x2 ≠ 0 := by
    intro h
    apply hx12
    linarith
  have hx13ne : x1 - x3 ≠ 0 := by
    intro h
    apply hx31
    linarith
  have eq12' : a * (x1 + x2) + b = 0 := by
    apply (mul_left_inj' hx12ne).mp
    linarith
  have eq13' : a * (x1 + x3) + b = 0 := by
    apply (mul_left_inj' hx13ne).mp
    linarith
  have h_eq3 : x1 + x2 = x1 + x3 := by
    have hne : a ≠ 0 := ha
    apply (mul_right_inj' hne).mp
    linarith
  have h_eq4 : x2 = x3 := by
    linarith
  -- Contradiction with the hypothesis $x2 \neq x3$.
  have hne : x2 ≠ x3 := hx23
  -- Applying the contradiction
  contradiction