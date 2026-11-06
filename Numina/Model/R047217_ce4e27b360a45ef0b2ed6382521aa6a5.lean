import Mathlib

theorem algebra_254144 {z : ℂ} (hz : Complex.abs (z + 2 * .I) = Complex.abs (z - 4 * .I)) (hz' : Complex.abs (z - 4) = 1) :
    z = 4 + .I := by 
  have h1 : z.im = 1 := by
    have h11 : Complex.abs (z + 2 * Complex.I) = Real.sqrt ((z.re)^2 + (z.im + 2)^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Complex.I_sq]
      <;> ring_nf
    have h12 : Complex.abs (z - 4 * Complex.I) = Real.sqrt ((z.re)^2 + (z.im - 4)^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Complex.I_sq]
      <;> ring_nf
    rw [h11, h12] at hz
    have h13 : (z.re)^2 + (z.im + 2)^2 = (z.re)^2 + (z.im - 4)^2 := by
      have h14 : Real.sqrt ((z.re)^2 + (z.im + 2)^2) = Real.sqrt ((z.re)^2 + (z.im - 4)^2) := hz
      have h15 : (Real.sqrt ((z.re)^2 + (z.im + 2)^2)) ^ 2 = (Real.sqrt ((z.re)^2 + (z.im - 4)^2)) ^ 2 := by
        rw [h14]
      rw [Real.sq_sqrt (by positivity), Real.sq_sqrt (by positivity)] at h15
      nlinarith
    ring_nf at h13
    nlinarith
  have h2 : z.re = 4 := by
    have h21 : Complex.abs (z - 4) = Real.sqrt ((z.re - 4)^2 + (z.im)^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Complex.I_sq]
      <;> ring_nf
    rw [h21] at hz'
    rw [Real.sqrt_eq_iff_sq_eq] at hz'
    · nlinarith [h1]
    all_goals nlinarith [h1]
  simp [Complex.ext_iff, h1, h2]
  all_goals norm_num