import Mathlib

theorem algebra_601002 (a b c d : ℝ) (P : ℝ → ℝ)
    (hP : ∀ x, P x = x ^ 4 + a * x ^ 3 + b * x ^ 2 + c * x + d)
    (hP1 : P 1 = 1993) (hP2 : P 2 = 3986) (hP3 : P 3 = 5979) :
    (P 11 + P (-7)) / 4 = 5233 := by
  have eq1 := hP 1
  rw [eq1] at hP1
  have eq2 := hP 2
  rw [eq2] at hP2
  have eq3 := hP 3
  rw [eq3] at hP3
  have eq11 := hP 11
  have eq7 := hP (-7)
  rw [eq11, eq7]
  linarith