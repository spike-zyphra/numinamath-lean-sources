import Mathlib

theorem algebra_95612 (x y : ℝ) (hx : x > 1) (hy : y > 0) :
    ∃ z, z > 0 ∧ x * z = y + z := by
  use y / (x - 1)
  have hx1_pos : x - 1 > 0 := by linarith
  constructor
  · -- Show that z > 0
    apply div_pos
    assumption
    linarith
  · -- Show x * z = y + z
    have hx1_ne_zero : x - 1 ≠ 0 := by
      linarith
    field_simp [hx1_ne_zero]
    <;> ring_nf <;> nlinarith