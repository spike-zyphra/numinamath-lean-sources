import Mathlib

theorem algebra_249480 {x y z : ℝ} (hx : x > 0) (hy : y > 0) (hz : z > 0)
    (h1 : x / y = 7 / 11) (h2 : x / z = 4 / 5) (h3 : y / z = 2 / 5) :
    x = 5.85 ∧ y = 3.15 := by
  have h4 : 11 * x = 7 * y := by
    have hne : y ≠ 0 := by linarith
    field_simp at h1 ⊢
    linarith
  have h5 : 5 * x = 4 * z := by
    have hne : z ≠ 0 := by linarith
    field_simp at h2 ⊢
    linarith
  have h6 : 5 * y = 2 * z := by
    have hne : z ≠ 0 := by linarith
    field_simp at h3 ⊢
    linarith

  have h7 : x = 0 := by 
    linarith [h4, h5, h6]
  linarith