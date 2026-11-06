import Mathlib

/-Consider the positive real numbers a, b, c, d, such that abcd = 1, calculate
E = (7 + a) / (1 + a + a * b + a * b * c) + (7 + b) / (1 + b + b * c + b * c * d) +
    (7 + c) / (1 + c + c * d + c * d * a) + (7 + d) / (1 + d + d * a + d * a * b) -/
theorem algebra_115869 (a b c d : ℝ) (h2 : 0 < a) (h3 : 0 < b) (h4 : 0 < c)
    (h1 : a * b * c * d = 1) :
    (7 + a) / (1 + a + a * b + a * b * c) + (7 + b) / (1 + b + b * c + b * c * d) +
    (7 + c) / (1 + c + c * d + c * d * a) + (7 + d) / (1 + d + d * a + d * a * b) = 8 := by

  -- we subsitute d by a and b and c --
  have h7 : d = 1 / (a * b * c) := by
    field_simp
    nlinarith
  -- plug d into the equation --
  rw [h7]
  field_simp
  ring
  