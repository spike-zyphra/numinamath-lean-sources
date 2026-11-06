import Mathlib

theorem algebra_21654 : ‖(-2 - 2 * √3 * Complex.I)^3‖ = 64 := by
  have h1 : ‖(-2 - 2 * √3 * Complex.I) ^ 3‖ = ‖(-2 - 2 * √3 * Complex.I)‖ ^ 3 := by
    simp [norm_pow]
  rw [h1]
  have h2 : ‖(-2 - 2 * √3 * Complex.I)‖ = 4 := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    ring_nf
    <;> norm_num [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf
    <;> norm_num
  rw [h2]
  all_goals norm_num