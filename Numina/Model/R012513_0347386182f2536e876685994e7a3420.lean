import Mathlib

theorem algebra_98087 {x : ℝ} (hx : x ≠ 1) (h : 1 - 1 / (1 - x) = 1 / (1 - x)) : x = -1 := by

  have h1 : 1 - x ≠ 0 := by
    intro h2
    apply hx
    linarith

  have eq1 : (1 - 1 / (1 - x)) * (1 - x) = (1 / (1 - x)) * (1 - x) := by
    rw [h]

  have eq2 : (1 - 1 / (1 - x)) * (1 - x) = -x := by
    have eq3 : 1 - x ≠ 0 := h1
    field_simp [eq3]
    <;> ring

  have eq3 : (1 / (1 - x)) * (1 - x) = 1 := by
    have eq4 : 1 - x ≠ 0 := h1
    field_simp [eq4]

  rw [eq2, eq3] at eq1
  linarith