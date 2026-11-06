import Mathlib

theorem algebra_8233 {x y : ℝ} (hx : x > 0) (hy : y > 0)
    (h1 : x * 1.5 = y * 0.9) (h2 : x * 2.4 = y * (1 + z)) :
    z = 44 / 100 := by
  have eq1 : y = (x * 1.5) / 0.9 := by
    field_simp at h1 ⊢
    nlinarith
  rw [eq1] at h2
  have h3 : x * 2.4 = ( (x * 1.5 ) / 0.9 ) * (1 + z ) := by 
    linarith
  have h4 : 2.4 * 0.9 = 1.5 * (1 + z) := by 
    have hx1 : x > 0 := hx
    have eq1 : x * 2.4 = ( (x * 1.5 ) / 0.9 ) * (1 + z ) := h2
    have eq2 : x * 2.4 * 0.9 = x * 1.5 * (1 + z) := by
      field_simp at eq1 ⊢
      nlinarith
    have eq3 : 2.4 * 0.9 = 1.5 * (1 + z) := by 
      apply (mul_left_inj' (show x ≠ 0 by linarith)).mp
      linarith
    linarith
  nlinarith