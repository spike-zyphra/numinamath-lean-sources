import Mathlib

theorem algebra_136775 (x y z : ℝ) (h1 : x - y + z - 2 = 0) (h2 : x - 2 * y - z + 4 = 0) :
    (x - 8) / 3 = (y - 6) / 2 ∧ (y - 6) / 2 = z / -1 := by
  have eq1 : y = (2 * x + 2) / 3 := by
    have h3 : 2 * x - 3 * y + 2 = 0 := by
      linarith [h1, h2]
    linarith [h3]
  have eq2 : z = (8 - x) / 3 := by 
    have h4 : x + 3 * z - 8 = 0 := by 
      linarith [h1, eq1]
    linarith [h4]
  constructor
  · -- Show (x - 8) / 3 = (y - 6) / 2
    rw [eq1]
    linarith
  · -- Show (y - 6) / 2 = z / -1
    rw [eq1, eq2]
    linarith