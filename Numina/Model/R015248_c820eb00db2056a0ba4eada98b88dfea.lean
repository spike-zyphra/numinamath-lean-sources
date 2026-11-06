import Mathlib

/- Given $z\in \mathbf{C}$, if the equation $4{{x}^{2}}-8zx+4\text{i}+3=0$ (where $\text{i}$ is the imaginary unit) has real roots, then the minimum value of the modulus of the complex number $z$, $\left| z \right|$, is ___          ___. -/
theorem algebra_11503 :
    IsLeast {x | ∃ z : ℂ, x = Complex.abs z ∧ ∃ r : ℝ, 4 * r ^ 2 - 8 * z * r + 4 * Complex.I + 3 = 0} 1 := by
  constructor
  · -- Show that 1 exists in the set
    use (Complex.mk (2 * Real.sqrt 5 / 5) (Real.sqrt 5 / 5))
    constructor
    · -- Show 1 = Complex.abs z
      simp [Complex.abs, Complex.normSq]
      ring_nf
      rw [Real.sq_sqrt (by norm_num)]
      <;> ring_nf <;> norm_num
    · -- Show that there exists a real root r
      use Real.sqrt 5 / 2
      simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_comm]
      field_simp
      ring_nf
      <;> norm_num [Real.sqrt_pos.mpr]
  · -- Show 1 is the least
    intro x hx
    rcases hx with ⟨z, h1, r, hr⟩
    have eq1 := congr_arg Complex.re hr
    have eq2 := congr_arg Complex.im hr
    simp [pow_two, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_comm] at eq1 eq2
    have h2 : z.im = 1 / (2 * r) := by
      have h8 : r ≠ 0 := by
        by_contra h
        rw [h] at eq2
        nlinarith
      have eq3 : z.im * (8 * r) = 4 := by
        nlinarith
      have h9 : (8 * r) ≠ 0 := by
        apply mul_ne_zero
        norm_num
        exact h8
      field_simp at eq3 ⊢
      nlinarith
    have h10 : z.re = (4 * r^2 + 3) / (8 * r) := by
      have h8 : r ≠ 0 := by
        by_contra h
        rw [h] at eq1
        nlinarith
      have eq3 : z.re * (8 * r) = 4 * r^2 + 3 := by
        nlinarith
      have h9 : (8 * r) ≠ 0 := by
        apply mul_ne_zero
        norm_num
        exact h8
      field_simp at eq3 ⊢
      nlinarith
    have h11 : Complex.abs z = Real.sqrt (z.re^2 + z.im^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Complex.I_sq]
      <;> ring
    rw [h11] at h1
    have eq3 : z.re^2 + z.im^2 = ((4 * r^2 + 3) / (8 * r))^2 + (1 / (2 * r))^2 := by
      rw [h10, h2]
      <;> ring_nf
    rw [eq3] at h1
    have h8 : r ≠ 0 := by
      by_contra h
      rw [h] at eq2
      norm_num at eq2
    have eq4 : ((4 * r^2 + 3) / (8 * r))^2 + (1 / (2 * r))^2 ≥ (1 : ℝ) := by
      have eq6 : ((4 * r^2 + 3) / (8 * r))^2 + (1 / (2 * r))^2 - (1 : ℝ) ≥ 0 := by
        have eq6 : ((4 * r^2 + 3) / (8 * r))^2 + (1 / (2 * r))^2 - (1 : ℝ) =
            ((4 * r^2 + 3)^2 + 16 - 64 * r^2) / (64 * r^2) := by
          field_simp
          <;> ring_nf
          <;> field_simp
          <;> ring
        rw [eq6]
        have h9 : r^2 > 0 := by
          apply sq_pos_of_ne_zero
          exact h8
        have h11 : (4 * r^2 + 3)^2 + 16 - 64 * r^2 ≥ 0 := by
          nlinarith [sq_nonneg (r^2 - 5 / 4), sq_nonneg (2 * r^2 - 5 / 2), sq_nonneg (4 * r^2 - 5), sq_nonneg (r^2), sq_nonneg ((4 : ℝ) * r ^ 2 - 5)]
        have h12 : 64 * r^2 > 0 := by
          nlinarith
        apply div_nonneg
        · linarith
        · linarith
      linarith
    have h9 : Real.sqrt (((4 * r^2 + 3) / (8 * r))^2 + (1 / (2 * r))^2) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (by linarith)
    have h2 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
    linarith [h9, h2, h1]