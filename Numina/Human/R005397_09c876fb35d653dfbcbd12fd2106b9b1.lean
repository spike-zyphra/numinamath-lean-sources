import Mathlib

/-A convex quadrilateral is determined by the points of intersection of the curves
x^4 + y^4 =100 and xy=4; determine its area.-/

theorem geometry_608136 {a b: ℝ} (h1: a ^ 4 + b ^ 4 = 100)
  (h2: a * b = 4): |(√2 * (a - b)) * (√2 * (a + b))| = 4 * √17 := by

  ring_nf
  have u: √2 ^ 2 = 2 := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    norm_num
    apply Real.sqrt_nonneg
  simp [u]
  rw [show 2 * a ^ 2 - 2 * b ^ 2 = 2 * (a ^ 2 - b ^ 2) by ring]
  rw [abs_mul]
  suffices |a ^ 2 - b ^ 2| = 2 * √17 by
    simp [this]
    ring
  have i: 0 ≤ √17 := by
    apply Real.sqrt_nonneg
  rw [show 2 * √17 = |2 * √17| by symm; apply abs_of_nonneg; linarith]
  rw [← sq_eq_sq_iff_abs_eq_abs]
  ring_nf
  have v: √17 ^ 2 = 17 := by
    symm
    rw [← Real.sqrt_eq_iff_eq_sq]
    norm_num
    apply Real.sqrt_nonneg
  simp [v]
  nlinarith
