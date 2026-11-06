import Mathlib

theorem algebra_231063 {w b : ℝ} (hw : w = 20 / 100 * b) (hb : b ≠ 0) :
    b / w - 1 = 400 / 100 := by

  have hw_eq2 : w = (1 / 5) * b := by
    linarith

  have hw_nonzero : w ≠ 0 := by
    intro h
    rw [h] at hw_eq2
    have : b = 0 := by
      linarith
    contradiction

  have h1 : b / w = 5 := by
    rw [hw_eq2]
    field_simp [show b ≠ 0 by exact hb]
    <;> ring

  rw [h1]
  norm_num