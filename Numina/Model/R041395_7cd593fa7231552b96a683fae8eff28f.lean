import Mathlib

theorem algebra_168345 (a b c : ℝ) (ha : 1 < a) (hb : a < b) (hc : b < c)
    (hsum : ∃ d, a + b = d ∧ a + c = d + a ∧ b + c = d + b ∧ a + b + c = d + c)
    (hsum' : ∃ d, a + b + c = d + a ∧ b + c = d + b ∧ a + c = d + c) :
    a = 10 ∧ b = 19 ∧ c = 37 ∨ a = 15 ∧ b = 22 ∧ c = 29 := by
  rcases hsum with ⟨d, h1, h2, h3, h4⟩
  rcases hsum' with ⟨d', h5, h6, h7⟩
  have eq5 : c = a + b := by
    nlinarith
  have eq6 : a + b + c = d' + a := h5
  have eq7 : b + c = d' + b := h6
  have eq8 : a + c = d' + c := h7
  have eq9 : b + c = d' := by
    nlinarith [eq6]
  have eq10 : c = d' := by
    nlinarith
  have eq11 : a = d' := by
    nlinarith [eq8]
  -- Note that from eq10, c = d', and from eq11, a = d', so a = c
  have eq12 : a = c := by
    linarith [eq11, eq10]
  -- Therefore `b < c` becomes `b < a`
  -- And `a < b` from hypothesis
  -- This is a contradiction
  nlinarith [show b < a from by
    nlinarith [eq12, hc]
  ]