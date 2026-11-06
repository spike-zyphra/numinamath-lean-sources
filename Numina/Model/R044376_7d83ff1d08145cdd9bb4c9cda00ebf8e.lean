import Mathlib
open Complex ComplexConjugate

theorem algebra_14821 :
  IsGreatest {x : ℝ | ∃ z w : ℂ, (abs z = 1 ∧ abs w = 1 ∧ z * (conj w) + w * (conj z) = 1 ∧ x = (z + w).re)} (√3) := by
  constructor
  · -- Show that √3 is achievable
    use { re := Real.sqrt 3 / 2, im := 1 / 2 }
    use { re := Real.sqrt 3 / 2, im := -1 / 2 }
    constructor
    · -- Show |z| = 1
      simp [Complex.abs, Complex.normSq]
      ring_nf
      norm_num [Real.sq_sqrt]
    constructor
    · -- Show |w| = 1
      simp [Complex.abs, Complex.normSq]
      ring_nf
      norm_num [Real.sq_sqrt]
    constructor
    · -- Show z * (conj w) + w * (conj z) = 1
      simp [Complex.ext_iff, pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring_nf
      norm_num [Real.sq_sqrt]
    · -- Show x = Re(z + w)
      simp [Complex.add_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.ofReal_im, Complex.I_im]
      all_goals ring_nf
  · -- Show that √3 is the greatest such value
    intro x hx
    rcases hx with ⟨z, w, h_abs_z, h_abs_w, h_eq, hx⟩
    have h1 : z.re ^ 2 + z.im ^ 2 = 1 := by
      have h_abs_z' : abs z = 1 := h_abs_z
      simp [Complex.abs, Complex.normSq] at h_abs_z'
      nlinarith
    have h2 : w.re ^ 2 + w.im ^ 2 = 1 := by
      have h_abs_w' : abs w = 1 := h_abs_w
      simp [Complex.abs, Complex.normSq] at h_abs_w'
      nlinarith
    have h6 : z.re * w.re + z.im * w.im = 1 / 2 := by
      have h4 : (z * (conj w) + w * (conj z)).re = 1 := by
        rw [h_eq]
        simp
      have h_eq_re : (z * (conj w) + w * (conj z)).re = 2 * (z.re * w.re + z.im * w.im) := by
        simp [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, Complex.I_im, Complex.conj_re, Complex.conj_im]
        all_goals ring
      rw [h_eq_re] at h4
      linarith
    have h7 : x = z.re + w.re := by
      simp [Complex.add_re, Complex.ofReal_re, Complex.I_re] at hx ⊢
      linarith
    have h9 : z.re + w.re ≤ Real.sqrt 3 := by
      have h8 : (z.re + w.re) ^ 2 ≤ 3 := by
        have h9 : (z.re + w.re) ^ 2 + (z.im + w.im) ^ 2 = 3 := by
          nlinarith [sq_nonneg (z.re - w.re), sq_nonneg (z.im - w.im), sq_nonneg (z.re + w.re), sq_nonneg (z.im + w.im)]
        nlinarith [sq_nonneg (z.im + w.im)]
      have h10 : (z.re + w.re) ^ 2 ≤ (3 : ℝ) := h8
      have h11 : (z.re + w.re) ≤ Real.sqrt 3 := by
        apply Real.le_sqrt_of_sq_le
        linarith
      linarith
    linarith [h7, h9]