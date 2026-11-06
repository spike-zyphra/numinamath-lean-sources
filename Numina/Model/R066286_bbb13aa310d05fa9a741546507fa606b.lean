import Mathlib

theorem algebra_290894 {a b c : ℝ} (h : a^2 + b = b^2 + c) (h' : b^2 + c = c^2 + a) :
    a * (a^2 - b^2) + b * (b^2 - c^2) + c * (c^2 - a^2) = 0 := by
  have eq1 : a^2 - b^2 = c - b := by
    nlinarith
  have eq2 : b^2 - c^2 = a - c := by
    nlinarith
  have eq3 : c^2 - a^2 = b - a := by
    nlinarith [h, h']
  have eq4 : a * (a^2 - b^2) = a * (c - b) := by
    rw [eq1]
  have eq5 : b * (b^2 - c^2) = b * (a - c) := by
    rw [eq2]
  have eq6 : c * (c^2 - a^2) = c * (b - a) := by
    rw [eq3]
  rw [eq4, eq5, eq6]
  ring