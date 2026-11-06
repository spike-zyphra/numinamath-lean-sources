import Mathlib

theorem algebra_278515 (d : ℝ) (h : d > 0) (v1 v2 : ℝ)
    (h1 : v1 = 60) (h2 : v2 = 90) :
    (2 * d) / (d / v1 + d / v2) = 72 := by
  rw [h1, h2]
  field_simp
  <;> ring_nf <;> norm_num
  <;> linarith