import Mathlib

theorem algebra_147846 {x y z : ℝ} (h : (x - 2) / 4 = (y - 1) / -3) (h' : (y - 1) / -3 = (z + 3) / -2)
    (h'' : 3 * x - y + 4 * z = 0) :
    x = 6 ∧ y = -2 ∧ z = -5 := by
  have eq1 : 3 * x + 4 * y = 10 := by
    linarith
  have eq2 : 2 * y - 3 * z = 11 := by
    linarith
  have hx : x = 6 := by
    linarith [eq1, eq2, h'']
  have hy : y = -2 := by
    linarith [eq1, hx]
  have hz : z = -5 := by
    linarith [eq2, hy]
  exact ⟨hx, hy, hz⟩