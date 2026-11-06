import Mathlib

theorem algebra_20241 (x : ℝ) (hx : x > 0) (h : 40 * 3 * x = y) :
    y / (4 * x) = 30 := by
  have hy : y = 120 * x := by
    linarith
  rw [hy]
  have hx' : x ≠ 0 := by linarith
  field_simp [hx']
  <;> ring_nf <;> field_simp [hx'] <;> ring