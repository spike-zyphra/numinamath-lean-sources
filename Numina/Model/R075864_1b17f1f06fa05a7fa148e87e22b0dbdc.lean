import Mathlib

theorem algebra_132821 (v : ℝ) (h : v > 0) (v' : ℝ) (h' : v' = 3 * v) :
    (2 * v * v') / (v + v') = 3 / 2 * v := by
  rw [h']
  field_simp
  <;> ring_nf <;> field_simp
  <;> nlinarith