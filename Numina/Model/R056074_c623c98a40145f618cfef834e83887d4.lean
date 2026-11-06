import Mathlib

theorem algebra_245315 {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (h1 : b = (2 / 3) * a) (h2 : a * (1 + 1 / 3) = b * (1 + 1 / 5)) (h3 : 190 / a = 190 / b + 1) :
    a * 2 = 400 := by
  rw [h1] at h2
  field_simp at h3
  nlinarith