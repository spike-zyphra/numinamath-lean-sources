import Mathlib

theorem algebra_193822 (v : ℝ) (h : v > 0) (h1 : (60 / (v + 15)) = (60 / v) - 12 / 60) :
    v = 60 := by
  have pos1 : v + 15 ≠ 0 := by
    linarith
  have pos2 : v ≠ 0 := by
    linarith
  have eq4 : 60 / (v + 15) = (60 / v) - 12 / 60 := h1
  field_simp [(show v + 15 ≠ 0 by linarith), (show v ≠ 0 by linarith)] at eq4
  have eq5 : v * (v + 15) = 4500 := by
    nlinarith
  have eq7 : v ^ 2 + 15 * v - 4500 = 0 := by
    nlinarith
  have eq8 : (v - 60) * (v + 75) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 eq8) with eq9 eq10
  · -- Solving for v - 60 = 0
    linarith
  · -- Solving for v + 75 = 0
    nlinarith