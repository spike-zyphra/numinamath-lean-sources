import Mathlib

theorem algebra_227782 (a b : ℂ) :
    ‖a + b‖^2 - ‖a - b‖^2 = 4 * (a.re * b.re + a.im * b.im) := by
  have h1 : ‖a + b‖^2 = (a.re + b.re)^2 + (a.im + b.im)^2 := by
    have h_mod_sq : ‖a + b‖ = Real.sqrt ((a.re + b.re)^2 + (a.im + b.im)^2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> simp [sq]
      <;> ring
    rw [h_mod_sq]
    rw [Real.sq_sqrt]
    all_goals nlinarith
  
  have h2 : ‖a - b‖^2 = (a.re - b.re)^2 + (a.im - b.im)^2 := by
    have h_mod_sq : ‖a - b‖ = Real.sqrt ((a.re - b.re)^2 + (a.im - b.im)^2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> simp [sq]
      <;> ring
    rw [h_mod_sq]
    rw [Real.sq_sqrt]
    all_goals nlinarith
  
  rw [h1, h2]
  nlinarith [sq_nonneg (a.re - b.re), sq_nonneg (a.re + b.re), sq_nonneg (a.im - b.im), sq_nonneg (a.im + b.im)]