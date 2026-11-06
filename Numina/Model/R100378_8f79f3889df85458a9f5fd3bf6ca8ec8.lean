import Mathlib

theorem algebra_20211 (v : ℝ) (h : v = 1.7 / 0.5) : 17 / v = 5 := by 
  rw [h]
  norm_num
  <;> try { field_simp }
  <;> norm_num