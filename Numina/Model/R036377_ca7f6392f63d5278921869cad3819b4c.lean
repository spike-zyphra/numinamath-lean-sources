import Mathlib

theorem algebra_129033 :
    ¬∃ a b c d : ℤ, a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d = 1 ∧ a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d = 2 := by
  rintro ⟨a, b, c, d, h1, h2⟩
  have eq1 : a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d - (a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d) = 1 := by
    linarith
  have eq2 : a * 62 ^ 3 + b * 62 ^ 2 + c * 62 + d - (a * 19 ^ 3 + b * 19 ^ 2 + c * 19 + d) =
    43 * (a * (62^2 + 62*19 + 19^2) + b * 81 + c) := by
    ring
  have eq3 : 43 * (a * (62^2 + 62*19 + 19^2) + b * 81 + c) = 1 := by
    linarith [eq1, eq2]
  have eq4 : a * (62^2 + 62*19 + 19^2) + b * 81 + c = 0 := by
    omega
  omega