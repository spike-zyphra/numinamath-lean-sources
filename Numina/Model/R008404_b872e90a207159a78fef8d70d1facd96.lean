import Mathlib

  theorem algebra_93720 {x : ℝ} (hx : x ≠ 0) (h : x = 2 + (-x) * (1 / x)) :
    0 < x ∧ x ≤ 2 := by
  have h1 : (-x) * (1 / x) = -1 := by 
    field_simp [hx]
    <;> linarith
  rw [h1] at h
  have hx_eq : x = 1 := by linarith 
  constructor
  · -- Show that 0 < x using h_eq
    linarith [hx_eq]
  · -- Show that x ≤ 2 using h_eq
    linarith [hx_eq]