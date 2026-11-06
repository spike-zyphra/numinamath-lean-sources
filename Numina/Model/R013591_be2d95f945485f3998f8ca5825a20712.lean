import Mathlib

theorem algebra_1524
(a : ℝ)
(h₀ : a ≠ 0)
(h₁ : -a * 94 * 3 * 27 * 5 = 19 * a * 94 * 3 * 27 * 5) :
a * (-a) * (1 / a) * 19 * 94 * 3 * 27 * 5 = -1 := by

  have h3 : a = 0 := by
    nlinarith

  contradiction