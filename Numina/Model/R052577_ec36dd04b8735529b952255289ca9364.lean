import Mathlib

theorem algebra_306962 {p d : ℝ} (hp : p > 0) (hd : 0 < d) (h : (1 + p / 100) * (1 - d / 100) = 1) :
    d = 100 * p / (100 + p) := by
  have h2 : (100 + p) ≠ 0 := by
    linarith
  field_simp [h2] at h ⊢
  nlinarith