import Mathlib

theorem algebra_130222 (a b c : ℝ) (ha : a ≠ 0) (hA : a * (-1) ^ 2 + b * (-1) + c = 0)
    (hB : a * 2 ^ 2 + b * 2 + c = 0) (hP : ∀ x, a * (x + 1) ^ 2 + b * (x + 1) + c ≠ 0)
    (x0 : ℝ) (hx0 : x0 ≠ -1) (hP1 : a * (x0 + 1) ^ 2 + b * (x0 + 1) + c = 2 * x0 ^ 2 - 2) :
    x0 + 1 = -1 ∧ 2 * x0 ^ 2 - 2 = 6 := by

  have eq1 : b = -a := by
    have eq2 : a * (-1) ^ 2 + b * (-1) + c = 0 := hA
    have eq3 : a * 2 ^ 2 + b * 2 + c = 0 := hB
    ring_nf at eq2 eq3
    have eq4 : c = b - a := by linarith
    rw [eq4] at eq3
    linarith

  have eq2 : c = -2 * a := by
    rw [eq1] at hA
    linarith

  have h1 := hP (-2)
  have eq3 : a * (-2 + 1) ^ 2 + b * (-2 + 1) + c = 0 := by
    rw [eq1, eq2]
    ring

  have eq4 : a * (-2 + 1) ^ 2 + b * (-2 + 1) + c ≠ 0 := h1
  contradiction