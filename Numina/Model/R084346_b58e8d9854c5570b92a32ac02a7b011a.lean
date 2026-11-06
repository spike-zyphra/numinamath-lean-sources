import Mathlib

theorem algebra_21469 {d p : ℝ} (hd : d > 0) (hp : p > 0) :
    (d * p) / (2 * d * 2 * p) = 1 / 4 := by
  have h1 : d * p ≠ 0 := by
    apply mul_ne_zero
    linarith
    linarith
  have h2 : 2 * d * 2 * p = 4 * (d * p) := by
    ring
  rw [h2]
  field_simp [h1]
  <;> ring_nf
  <;> field_simp [h1]
  <;> linarith