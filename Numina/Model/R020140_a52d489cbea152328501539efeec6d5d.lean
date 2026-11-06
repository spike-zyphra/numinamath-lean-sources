import Mathlib

theorem algebra_26247 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h1 : 1 / (3 * a) + 1 / b = 2011) (h2 : 1 / a + 1 / (3 * b) = 1) :
    (a + b) / (a * b) = 1509 := by

  have eq1 : (1 / (3 * a) + 1 / b) + (1 / a + 1 / (3 * b)) = 2011 + 1 := by
    linarith [h1, h2]

  have eq2 : (1 / (3 * a) + 1 / b) + (1 / a + 1 / (3 * b)) = 4 / 3 * (1 / a + 1 / b) := by 
    field_simp [ha, hb]
    <;> ring

  have eq3 : (1 / a + 1 / b) = 1509 := by
    have eq4 : (1 / (3 * a) + 1 / b) + (1 / a + 1 / (3 * b)) = 2011 + 1 := by
      linarith [h1, h2]
    have eq5 : (1 / (3 * a) + 1 / b) + (1 / a + 1 / (3 * b)) = 4 / 3 * (1 / a + 1 / b) := by 
      field_simp [ha, hb]
      <;> ring
    rw [eq5] at eq4 
    linarith

  have eq4 : (a + b) / (a * b) = 1 / a + 1 / b := by
    field_simp [ha, hb]
    <;> ring

  rw [eq4]
  linarith [eq3]