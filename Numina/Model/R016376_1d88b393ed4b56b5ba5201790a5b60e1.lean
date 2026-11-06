import Mathlib

theorem algebra_191156 (a b c : ℝ) (h : ∀ x : ℝ, (x + a)^2 + (2 * x + b)^2 + (2 * x + c)^2 = (3 * x + 1)^2) :
    a = 1 / 3 ∧ b = 2 / 3 ∧ c = 2 / 3 := by

  have eq1 := h 0
  have eq2 := h 1
  have eq3 := h 2
  have eq4 := h 3

  have h1 : a ^ 2 + b ^ 2 + c ^ 2 = 1 := by
    nlinarith [eq1]

  have h2 : a + 2 * b + 2 * c = 3 := by
    ring_nf at eq1 eq2 eq3 eq4
    nlinarith

  have ha : a = 1 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 2 / 3), sq_nonneg (c - 2 / 3), h1, h2]

  have hb : b = 2 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 2 / 3), sq_nonneg (c - 2 / 3), h1, h2]

  have hc : c = 2 / 3 := by
    nlinarith [sq_nonneg (a - 1 / 3), sq_nonneg (b - 2 / 3), sq_nonneg (c - 2 / 3), h1, h2]

  exact ⟨ha, hb, hc⟩