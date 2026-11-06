import Mathlib

theorem algebra_20227 {p q : ℝ} (hp : 1 < p) (hq : 1 < q) (h : 1 / p + 1 / q = 1) :
    (p - 1) * (q - 1) = 1 := by
  have h1 : p + q = p * q := by
    have hp2 : 0 < p := by linarith
    have hq2 : 0 < q := by linarith
    field_simp at h
    linarith
  have h2 : (p - 1) * (q - 1) = p * q - (p + q) + 1 := by 
    ring
  rw [h2, h1]
  linarith