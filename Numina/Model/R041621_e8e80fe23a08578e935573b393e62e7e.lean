import Mathlib

theorem algebra_147797 (z : ℂ) (h : ∃ x : ℝ, 4 * x ^ 2 - 8 * z * x + 4 * Complex.I + 3 = 0) :
    Complex.abs z ≥ 1 := by
  rcases h with ⟨x, hx⟩
  have eq1 := congr_arg Complex.re hx
  have eq2 := congr_arg Complex.im hx
  simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im] at eq1 eq2
  have h1 : -8 * (z.im) * x + 4 = 0 := by linarith [eq2]
  have h3 : 4 * x ^ 2 - 8 * z.re * x + 3 = 0 := by linarith [eq1]
  have h2 : z.im = 1 / (2 * x) := by
    have hx0 : x ≠ 0 := by
      by_contra h0
      rw [h0] at h1
      linarith
    field_simp [hx0]
    linarith
  have h4 : z.re = (4 * x ^ 2 + 3) / (8 * x) := by
    have hx0 : x ≠ 0 := by
      by_contra h0
      rw [h0] at h1
      linarith
    field_simp [hx0]
    linarith
  have h5 : z.re ^ 2 + z.im ^ 2 ≥ 1 := by
    have hx0 : x ≠ 0 := by
      by_contra h0
      rw [h0] at h1
      linarith
    have h6 : z.re ^ 2 + z.im ^ 2 = ((4 * x ^ 2 + 3) ^ 2 + 16) / (64 * x ^ 2) := by
      rw [h4, h2]
      field_simp [hx0]
      ring
    rw [h6]
    have hx1 : x ^ 2 > 0 := by
      have hx0' : x ≠ 0 := hx0
      have : x ^ 2 > 0 := by
        exact sq_pos_of_ne_zero hx0'
      linarith
    have h8 : (4 * x ^ 2 + 3) ^ 2 + 16 ≥ 64 * x ^ 2 := by
      nlinarith [sq_nonneg (4 * x ^ 2 - 5)]
    have hx2 : 64 * x ^ 2 > 0 := by
      nlinarith
    apply (le_div_iff₀ hx2).mpr
    linarith
    all_goals nlinarith
  have h6 : Complex.abs z = Real.sqrt (z.re ^ 2 + z.im ^ 2) := by
    simp [Complex.abs, Complex.normSq]
    <;> ring
  rw [h6]
  have h7 : Real.sqrt (z.re ^ 2 + z.im ^ 2) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (show (z.re ^ 2 + z.im ^ 2) ≥ 1 by linarith [h5])
  have h8 : Real.sqrt (1 : ℝ) = (1 : ℝ) := Real.sqrt_one
  rw [h8] at h7
  linarith