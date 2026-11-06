import Mathlib

theorem algebra_276125 {a b c d : ℤ} (h1 : a * c + a * d + b * c + b * d = 68) (h2 : c + d = 4) :
    a + b + c + d = 21 := by
  have h3 : a * c + a * d + b * c + b * d = (a + b) * (c + d) := by
    ring
  rw [h3] at h1
  have h4 : (a + b) * 4 = 68 := by
    rw [h2] at h1
    linarith
  have h5 : a + b = 17 := by
    omega
  linarith [h5, h2]