import Mathlib

theorem algebra_137846 (x y z : ℝ) (h1 : x + 5 * y - z - 5 = 0) (h2 : 2 * x - 5 * y + 2 * z + 5 = 0) :
    x / 5 = (y - 1) / -4 ∧ (y - 1) / -4 = z / -15 := by
  have h3 : z = -3 * x := by
    have h4 : 3 * x + z = 0 := by
      linarith
    linarith
  -- Substitute z = -3 * x into the first equation
  have h4 : y = 1 - (4 / 5) * x := by
    have eq1 := h1
    rw [show z = -3 * x by linarith [h3]] at eq1
    linarith
  constructor
  · -- Prove the first part: x / 5 = (y - 1) / -4
    have eq1 : y - 1 = - (4 / 5) * x := by
      linarith [h4]
    field_simp [eq1]
    <;> linarith
  · -- Prove the second part: (y - 1) / -4 = z / -15
    have eq1 : y - 1 = - (4 / 5) * x := by
      linarith [h4]
    have eq2 : z = -3 * x := by
      linarith [h3]
    field_simp [eq1, eq2]
    <;> linarith