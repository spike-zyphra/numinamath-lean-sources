import Mathlib

theorem algebra_139434 (z : ℂ) (h : ∃ x : ℝ, x^2 - 2 * z * x + 3 / 4 + .I = 0) :
    Complex.abs z ≥ 1 := by 
  rcases h with ⟨x, hx⟩
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_add, mul_comm, mul_assoc] at eq1 eq2 
  -- Separate into real and imaginary parts:
  -- Real part: x^{2} - 2 a x + 3 / 4 = 0
  -- Imaginary part: -2 b x + 1 = 0
  have h1 : (x : ℝ) ^ 2 - 2 * (z.re : ℝ) * x + 3 / 4 = 0 := by 
    nlinarith
  have h2 : (-2 * (z.im : ℝ) * x + 1) = 0 := by 
    nlinarith
  have hx1 : x ≠ 0 := by 
    by_contra h'
    have h5 : x = 0 := by nlinarith
    rw [h5] at h2
    nlinarith 
  have h3 : z.im = 1 / (2 * x) := by
    have h10 : x ≠ 0 := hx1
    field_simp
    nlinarith
  have h4 : z.re = (x ^ 2 + 3 / 4) / (2 * x) := by
    have h10 : x ≠ 0 := hx1
    field_simp
    nlinarith 
  have h5 : z.re ^ 2 + z.im ^ 2 ≥ 1 := by
    have h9 : z.re ^ 2 = ((x ^ 2 + 3 / 4) / (2 * x)) ^ 2 := by 
      rw [h4]
    have h10 : z.im ^ 2 = (1 / (2 * x)) ^ 2 := by 
      rw [h3]
    rw [h9, h10]
    have hx5 : x ≠ 0 := hx1
    have hx10 : (x : ℝ) ^ 2 > 0 := by 
      nlinarith [sq_nonneg x, hx5]
    -- The inequality (x^{2} + 3 / 4) / (2x) includes the smallest norm vector c_n.
    have h6 : ((x ^ 2 + 3 / 4) / (2 * x)) ^ 2 + (1 / (2 * x)) ^ 2 - 1 ≥ 0 := by 
      have hx7 : 4 * x ^ 2 > 0 := by 
        nlinarith [sq_pos_of_ne_zero hx5]
      have h7 : ((x ^ 2 + 3 / 4) / (2 * x)) ^ 2 + (1 / (2 * x)) ^ 2 - 1 =
          ((x ^ 2 + 3 / 4) ^ 2 + 1 - 4 * x ^ 2) / (4 * x ^ 2) := by
        field_simp
        ring
      rw [h7]
      have hx4 : ((x ^ 2 + 3 / 4) ^ 2 + 1 - 4 * x ^ 2) / (4 * x ^ 2) ≥ 0 := by 
        apply div_nonneg 
        nlinarith [sq_nonneg ((x : ℝ) ^ 2 - 5 / 4)]
        linarith [hx7]
      linarith
    nlinarith
  have h6 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by 
    simp [Complex.abs, Complex.normSq]
    <;> ring_nf 
  rw [h6]
  have h7 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≥ Real.sqrt (1 : ℝ) := by 
    apply Real.sqrt_le_sqrt 
    linarith 
  have h8 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one 
  linarith