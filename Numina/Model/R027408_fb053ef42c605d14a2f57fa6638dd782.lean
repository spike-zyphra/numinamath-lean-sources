import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem calculus_15824 {w z : ℂ} (hw : w * z = 12 - 8 * .I) (h : ‖w‖ = Real.sqrt 13) :
    ‖z‖ = 4 := by
  have h1 : ‖w * z‖ = ‖w‖ * ‖z‖ := by
    simp [norm_mul]
  have h2 : ‖w * z‖ = Real.sqrt 208 := by
    rw [hw]
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    ring_nf
  have h3 : Real.sqrt 208 = 4 * Real.sqrt 13 := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> ring_nf <;> norm_num
  rw [h3] at h2
  rw [h1] at h2
  rw [h] at h2
  have h4 : Real.sqrt 13 * ‖z‖ = 4 * Real.sqrt 13 := by
    simpa using h2
  have h5 : Real.sqrt 13 > 0 := by
    apply Real.sqrt_pos.mpr
    norm_num
  have : ‖z‖ = 4 := by
    apply (mul_left_inj' (ne_of_gt h5)).mp
    linarith
  exact_mod_cast this