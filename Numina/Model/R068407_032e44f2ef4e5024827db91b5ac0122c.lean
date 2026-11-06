import Mathlib

theorem algebra_227791 (z w : ℂ) :
    (‖z + w‖^2 + ‖z - w‖^2) = (2 * ‖z‖^2 + 2 * ‖w‖^2) := by
  have h1 : ‖z‖ = Real.sqrt (z.re^2 + z.im^2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  have h1' : ‖w‖ = Real.sqrt (w.re^2 + w.im^2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  have h2 : ‖z + w‖ = Real.sqrt ((z.re + w.re)^2 + (z.im + w.im)^2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  have h3 : ‖z - w‖ = Real.sqrt ((z.re - w.re)^2 + (z.im - w.im)^2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> norm_num
    <;> ring
  rw [h2, h3, h1, h1']
  have h4 : (Real.sqrt ((z.re + w.re)^2 + (z.im + w.im)^2)) ^ 2 = (z.re + w.re)^2 + (z.im + w.im)^2 := Real.sq_sqrt (by positivity)
  have h5 : (Real.sqrt ((z.re - w.re)^2 + (z.im - w.im)^2)) ^ 2 = (z.re - w.re)^2 + (z.im - w.im)^2 := Real.sq_sqrt (by positivity)
  have h6 : (Real.sqrt (z.re^2 + z.im^2)) ^ 2 = z.re^2 + z.im^2 := Real.sq_sqrt (by positivity)
  have h7 : (Real.sqrt (w.re^2 + w.im^2)) ^ 2 = w.re^2 + w.im^2 := Real.sq_sqrt (by positivity)
  rw [h4, h5, h6, h7]
  all_goals
    ring_nf
    <;> norm_num
    <;> ring