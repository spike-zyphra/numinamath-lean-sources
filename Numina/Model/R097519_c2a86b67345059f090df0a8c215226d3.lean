import Mathlib

theorem algebra_9507 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h1 : x = y + z - 1) (h2 : y + z - 1 = 4 - y - 2 * z) :
    y = 3 * x - 2 ∧ z = -2 * x + 3 := by
  have eq2 : 2 * y + 3 * z = 5 := by 
    linarith
  have eq1 : y + z = x + 1 := by
    linarith
  have eq3 : y = 3 * x - 2 := by
    have hz' : z = x + 1 - y := by linarith [eq1]
    rw [hz'] at eq2
    linarith
  have eq4 : z = -2 * x + 3 := by 
    have hz' : z = x + 1 - y := by linarith [eq1]
    rw [hz', eq3]
    linarith
  constructor
  · exact eq3
  · exact eq4