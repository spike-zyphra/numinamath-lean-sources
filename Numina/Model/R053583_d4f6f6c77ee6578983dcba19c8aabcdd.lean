import Mathlib

theorem algebra_276112 (a b c d : ℤ) :
    (a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d ≠ 1) ∨
    (a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d ≠ 2) := by
  by_contra h
  push_neg at h
  have h1 : a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d = 1 := h.1
  have h2 : a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d = 2 := h.2
  have eq1 : a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d - (a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d) = 1 := by
    linarith
  have eq2 : 43 * (a * (62 ^ 2 + 62 * 19 + 19 ^ 2) + b * (62 + 19) + c) = 1 := by
    linarith [eq1]
  -- This is clearly a contradiction because 43 cannot divide 1
  omega