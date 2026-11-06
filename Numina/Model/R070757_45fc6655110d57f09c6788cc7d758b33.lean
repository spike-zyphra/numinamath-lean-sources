import Mathlib

theorem algebra_21238 : ‖9 * Complex.I - 12‖ * ‖3 + 4 * Complex.I‖ = 75 := by
  have h1 : ‖9 * Complex.I - 12‖ = 15 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    ring_nf
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> linarith
  have h2 : ‖3 + 4 * Complex.I‖ = 5 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    ring_nf
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
    <;> linarith
  rw [h1, h2]
  all_goals norm_num