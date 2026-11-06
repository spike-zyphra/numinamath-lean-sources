import Mathlib

theorem algebra_314840 (z : ℂ) (h : ∃ x : ℝ, 4 * x ^ 2 - 8 * z * x + 4 * .I + 3 = 0) :
    Complex.abs z ≥ 1 := by
  rcases h with ⟨x, hx⟩
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_add, mul_assoc] at eq1 eq2
  have eq3 : (4 * x ^ 2 - 8 * z.re * x + 3) = 0 := by
    nlinarith
  have eq4 : -8 * z.im * x + 4 = 0 := by
    nlinarith
  have hz1 : z.im = 1 / (2 * x) := by
    have h2 : x ≠ 0 := by
      by_contra h3
      have : x = 0 := by linarith
      rw [this] at eq4
      norm_num at eq4
    field_simp
    <;> nlinarith
  have hz2 : z.re = (4 * x ^ 2 + 3) / (8 * x) := by
    have h2 : x ≠ 0 := by
      by_contra h3
      have : x = 0 := by linarith
      rw [this] at eq3
      norm_num at eq3
    field_simp
    <;> nlinarith
  have h1 : z.re ^ 2 + z.im ^ 2 ≥ 1 := by 
    rw [hz2, hz1]
    have h2 : x ≠ 0 := by
      by_contra h3
      have : x = 0 := by linarith
      rw [this] at eq4
      norm_num at eq4
    have eq6 : ((4 * x ^ 2 + 3) / (8 * x)) ^ 2 + (1 / (2 * x)) ^ 2 - 1 ≥ 0 := by 
      have h9 : ((4 * x ^ 2 + 3) / (8 * x)) ^ 2 + (1 / (2 * x)) ^ 2 - 1 = (16 * x ^ 4 - 40 * x ^ 2 + 25) / (64 * x ^ 2) := by 
        field_simp
        <;> ring_nf
      rw [h9]
      have h10 : (16 * x ^ 4 - 40 * x ^ 2 + 25 : ℝ) = (4 * x ^ 2 - 5) ^ 2 := by 
        nlinarith
      have h11 : (4 * x ^ 2 - 5) ^ 2 ≥ 0 := by 
        apply sq_nonneg
      have h12 : x ^ 2 > 0 := by 
        have h13 : x ≠ 0 := h2
        have h14 : x ^ 2 > 0 := by
          apply sq_pos_of_ne_zero
          exact h13
        linarith
      have h15 : (16 * x ^ 4 - 40 * x ^ 2 + 25) ≥ 0 := by 
        linarith [h10, h11]
      have h16 : (64 * x ^ 2) > 0 := by
        nlinarith [h12]
      apply div_nonneg 
      linarith 
      linarith 
    have eq7 : ((4 * x ^ 2 + 3) / (8 * x)) ^ 2 + (1 / (2 * x)) ^ 2 ≥ 1 := by 
      linarith [eq6]
    linarith
  have h3 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf
  rw [h3]
  have h4 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≥ Real.sqrt (1 : ℝ) := by 
    apply Real.sqrt_le_sqrt
    linarith [h1]
  have h5 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
  linarith