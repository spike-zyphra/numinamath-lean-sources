import Mathlib

theorem algebra_257514 (d : ℝ) (h₀ : d > 0) :
    (d / 80) + (d / 80) < (d / 90) + (d / 70) := by 
  have h1 : (d / 80) + (d / 80) = d / 40 := by 
    ring
  have h2 : (d / 90) + (d / 70) = (8 * d) / 315 := by 
    field_simp
    ring_nf
  rw [h1, h2]
  linarith