import Mathlib

theorem algebra_253727 {z1 z2 z3 : ℂ} (h1 : ‖z1‖ = ‖z2 + z3‖) (h2 : ‖z2‖ = ‖z3 + z1‖)
    (h3 : ‖z3‖ = ‖z1 + z2‖) : z1 + z2 + z3 = 0 := by
  have eq1 : z1.re ^ 2 + z1.im ^ 2 = (z2.re + z3.re) ^ 2 + (z2.im + z3.im) ^ 2 := by
    have h1_mod : ‖z1‖ = ‖z2 + z3‖ := h1
    have h1_mod1 : ‖z1‖ = Real.sqrt (z1.re ^ 2 + z1.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    have h1_mod2 : ‖z2 + z3‖ = Real.sqrt ((z2.re + z3.re) ^ 2 + (z2.im + z3.im) ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im]
      <;> ring_nf
    rw [h1_mod1, h1_mod2] at h1_mod
    have h1_sqr : z1.re ^ 2 + z1.im ^ 2 = (z2.re + z3.re) ^ 2 + (z2.im + z3.im) ^ 2 := by
      have h1_eq : Real.sqrt (z1.re ^ 2 + z1.im ^ 2) = Real.sqrt ((z2.re + z3.re) ^ 2 + (z2.im + z3.im) ^ 2) := by linarith
      have h1_nonneg1 : z1.re ^ 2 + z1.im ^ 2 ≥ 0 := by positivity
      have h1_nonneg2 : (z2.re + z3.re) ^ 2 + (z2.im + z3.im) ^ 2 ≥ 0 := by positivity
      have h1_eq2 : z1.re ^ 2 + z1.im ^ 2 = (z2.re + z3.re) ^ 2 + (z2.im + z3.im) ^ 2 := by
        rw [Real.sqrt_inj (by positivity) (by positivity) ] at h1_eq
        linarith
      linarith
    exact h1_sqr
  -- Second equation in terms of real and imaginary parts
  have eq2 : z2.re ^ 2 + z2.im ^ 2 = (z3.re + z1.re) ^ 2 + (z3.im + z1.im) ^ 2 := by
    have h2_mod : ‖z2‖ = ‖z3 + z1‖ := h2
    have h2_mod1 : ‖z2‖ = Real.sqrt (z2.re ^ 2 + z2.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    have h2_mod2 : ‖z3 + z1‖ = Real.sqrt ((z3.re + z1.re) ^ 2 + (z3.im + z1.im) ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im]
      <;> ring_nf
    rw [h2_mod1, h2_mod2] at h2_mod
    have h1_sqr : z2.re ^ 2 + z2.im ^ 2 = (z3.re + z1.re) ^ 2 + (z3.im + z1.im) ^ 2 := by
      have h1_eq : Real.sqrt (z2.re ^ 2 + z2.im ^ 2) = Real.sqrt ((z3.re + z1.re) ^ 2 + (z3.im + z1.im) ^ 2) := by linarith
      have h1_nonneg1 : z2.re ^ 2 + z2.im ^ 2 ≥ 0 := by positivity
      have h1_nonneg2 : (z3.re + z1.re) ^ 2 + (z3.im + z1.im) ^ 2 ≥ 0 := by positivity
      have h1_eq2 : z2.re ^ 2 + z2.im ^ 2 = (z3.re + z1.re) ^ 2 + (z3.im + z1.im) ^ 2 := by
        rw [Real.sqrt_inj (by positivity) (by positivity) ] at h1_eq
        linarith
      linarith
    exact h1_sqr
  -- Third equation in terms of real and imaginary parts
  have eq3 : z3.re ^ 2 + z3.im ^ 2 = (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 := by
    have h3_mod : ‖z3‖ = ‖z1 + z2‖ := h3
    have h3_mod1 : ‖z3‖ = Real.sqrt (z3.re ^ 2 + z3.im ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq]
      <;> ring_nf
    have h3_mod2 : ‖z1 + z2‖ = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by
      simp [Complex.norm_eq_abs, Complex.abs, Complex.normSq, Complex.add_re, Complex.add_im]
      <;> ring_nf
    rw [h3_mod1, h3_mod2] at h3_mod
    have h3_sqr : z3.re ^ 2 + z3.im ^ 2 = (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 := by
      have h1_eq : Real.sqrt (z3.re ^ 2 + z3.im ^ 2) = Real.sqrt ((z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2) := by linarith
      have h1_nonneg1 : z3.re ^ 2 + z3.im ^ 2 ≥ 0 := by positivity
      have h1_nonneg2 : (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 ≥ 0 := by positivity
      have h1_eq2 : z3.re ^ 2 + z3.im ^ 2 = (z1.re + z2.re) ^ 2 + (z1.im + z2.im) ^ 2 := by
        rw [Real.sqrt_inj ( by positivity) (by positivity) ] at h1_eq
        linarith
      linarith
    exact h3_sqr
  have eq7 : z1.re + z2.re + z3.re = 0 := by
    nlinarith [sq_nonneg (z1.re + z2.re + z3.re), sq_nonneg (z1.im + z2.im + z3.im),
      sq_nonneg (z1.re), sq_nonneg (z1.im), sq_nonneg (z2.re), sq_nonneg (z2.im), sq_nonneg (z3.re), sq_nonneg (z3.im)]
  have eq8 : z1.im + z2.im + z3.im = 0 := by
    nlinarith [sq_nonneg (z1.re + z2.re + z3.re), sq_nonneg (z1.im + z2.im + z3.im),
      sq_nonneg (z1.re), sq_nonneg (z1.im), sq_nonneg (z2.re), sq_nonneg (z2.im), sq_nonneg (z3.re), sq_nonneg (z3.im)]
  have h9 : z1 + z2 + z3 = 0 := by
    simp [Complex.ext_iff, eq7, eq8]
    <;> try nlinarith
  exact h9