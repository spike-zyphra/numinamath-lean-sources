import Mathlib

theorem algebra_243953 (z w : ℂ) (hz : ‖z + w‖ = Real.sqrt 3) (hw : ‖z‖ = 1) (h : ‖w‖ = 1) :
    ‖z - w‖ = 1 := by
  have h2 : ‖z‖ = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf
  have h3 : ‖w‖ = Real.sqrt (w.re ^ 2 + w.im ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf
  have h4 : ‖z + w‖ = Real.sqrt ((z.re + w.re) ^ 2 + (z.im + w.im) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf
  have h5 : ‖z - w‖ = Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) := by
    simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
    <;> ring_nf <;> simp [Real.sqrt_eq_iff_sq_eq]
    <;> ring_nf
  rw [h4] at hz
  rw [h2] at hw
  rw [h3] at h
  rw [h5]
  have h2' : z.re ^ 2 + z.im ^ 2 = 1 := by
    have h2' : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = (1) ^ 2 := by rw [hw]
    have h_nonneg : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
    have h_eq : (Real.sqrt (z.re ^ 2 + z.im ^ 2)) ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith
  have h3' : w.re ^ 2 + w.im ^ 2 = 1 := by
    have h3' : (Real.sqrt (w.re ^ 2 + w.im ^ 2)) ^ 2 = (1) ^ 2 := by rw [h]
    have h_nonneg : 0 ≤ w.re ^ 2 + w.im ^ 2 := by positivity
    have h_eq : (Real.sqrt (w.re ^ 2 + w.im ^ 2)) ^ 2 = w.re ^ 2 + w.im ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith
  have h4' : (z.re + w.re) ^ 2 + (z.im + w.im) ^ 2 = 3 := by
    have h4' : (Real.sqrt ((z.re + w.re) ^ 2 + (z.im + w.im) ^ 2)) ^ 2 = (Real.sqrt 3) ^ 2 := by
      rw [hz]
    have h_nonneg : 0 ≤ (z.re + w.re) ^ 2 + (z.im + w.im) ^ 2 := by positivity
    have h_eq : (Real.sqrt ((z.re + w.re) ^ 2 + (z.im + w.im) ^ 2)) ^ 2 = (z.re + w.re) ^ 2 + (z.im + w.im) ^ 2 := by
      rw [Real.sq_sqrt]
      nlinarith
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have h8 : (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 = 1 := by
    nlinarith
  have h9 : Real.sqrt ((z.re - w.re) ^ 2 + (z.im - w.im) ^ 2) = Real.sqrt 1 := by
    rw [h8]
  rw [h9]
  simp
  all_goals nlinarith