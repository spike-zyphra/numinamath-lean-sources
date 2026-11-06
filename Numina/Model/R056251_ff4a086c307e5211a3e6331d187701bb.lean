import Mathlib

theorem algebra_936
    (a b c M N : ℝ)
    (h₁ : 1^3 + a * 1^2 + b * 1 + c = 1)
    (h₂ : 2^3 + a * 2^2 + b * 2 + c = 2)
    (h₃ : 8^3 + a * 8^2 + b * 8 + c = M)
    (h₄ : (-5)^3 + a * (-5)^2 + b * (-5) + c = N) :
    M - N = 559 := by
  have eq1 : a + b + c = 0 := by
    linarith
  have eq2 : 4 * a + 2 * b + c = -6 := by
    linarith
  have eq3 : M = 512 + 64 * a + 8 * b + c := by
    linarith
  have eq4 : N = -125 + 25 * a - 5 * b + c := by
    linarith
  have eq5 : M - N = 559 := by
    rw [eq3, eq4]
    linarith [eq1, eq2]
  linarith [eq5]