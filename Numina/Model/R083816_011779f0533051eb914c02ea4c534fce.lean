import Mathlib

theorem algebra_178537 {m1 m2 l : ℝ} (hm1 : m1 = 0.5) (hm2 : m2 = 2) (hl : l > 0)
    (h1 : m1 / l = m2 / (l * 3)) (h2 : m2 / l = m1 / (l * 3) + l) :
    l = 0.875 := by 
  rw [hm1] at h1 h2
  rw [hm2] at h1 h2 
  have h3 : l > 0 := hl 
  field_simp [show l ≠ 0 by linarith] at h1 h2 
  ring_nf at h1 h2 
  nlinarith