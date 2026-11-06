import Mathlib

theorem algebra_106479 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : (x * 0.76 + y * 0.75) / (x + y) = 0.24) (h2 : y / (x + y) = 0.25) :
    (x * 0.76 + y * 0.75) / (x + y) = 0.28 := by 
  have h3 : x + y ≠ 0 := by
    nlinarith
  have eq1 : x * 0.76 + y * 0.75 = 0.24 * (x + y) := by
    have denom : (x + y) ≠ 0 := by nlinarith
    field_simp [denom] at h1 ⊢
    linarith
  have eq2 : y = 0.25 * (x + y) := by
    have denom : (x + y) ≠ 0 := by nlinarith
    field_simp [denom] at h2 ⊢
    linarith
  have eq3 : x = 3 * y := by
    ring_nf at eq2
    nlinarith
  rw [eq3] at eq1
  nlinarith