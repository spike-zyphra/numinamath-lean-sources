import Mathlib

theorem algebra_240824 : IsLeast {S : ℝ | ∃ z : ℂ, ((∃ x : ℝ, x^2 - 2 * z * x + 3 / 4 + Complex.I = 0) ∧ S = Complex.abs z)} 1:= by
  constructor
  · -- Show 1 in the given set.
    use (2 / Real.sqrt 5 + (1 / Real.sqrt 5) * Complex.I)
    constructor
    · -- Show existence of a real root
      use (Real.sqrt 5 / 2)
      field_simp [pow_two, Complex.ext_iff, mul_add, mul_comm, mul_assoc, Complex.I_mul_I]
      <;> ring_nf
      <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
      <;> ring_nf
      <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
      <;> ring_nf
      <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
      <;> ring_nf <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
      <;> tauto
      <;> ring_nf
      <;> norm_num [Real.sqrt_nonneg, Real.sq_sqrt]
    · -- Show the modulus is 1
      have h1 : Real.sqrt 5 ^ 2 = 5 := by
        rw [Real.sq_sqrt]
        all_goals norm_num
      have h2 : Complex.abs (2 / Real.sqrt 5 + (1 / Real.sqrt 5) * Complex.I) = Real.sqrt ((2 / Real.sqrt 5) ^ 2 + (1 / Real.sqrt 5) ^ 2) := by
        simp [Complex.abs, Complex.normSq]
        <;> ring_nf <;> simp [Complex.normSq]
        <;> ring
      rw [h2]
      have h7 : (2 / Real.sqrt 5 : ℝ) ^ 2 + (1 / Real.sqrt 5 : ℝ) ^ 2 = 1 := by
        have h1' : Real.sqrt 5 ^ 2 = 5 := h1
        field_simp [h1']
        <;> nlinarith
        <;> tauto
      rw [h7]
      simp
  · -- Show 1 is the least
    intro S hS
    rcases hS with ⟨z, ⟨x, hx⟩, hS⟩
    have eq1 := congr_arg Complex.re hx
    have eq2 := congr_arg Complex.im hx
    simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_add, mul_comm, mul_assoc] at eq1 eq2
    have h1 : x ≠ 0 := by
      by_contra h
      rw [h] at eq2
      nlinarith
    have h2 : z.im = 1 / (2 * x) := by
      have hne : x ≠ 0 := h1
      have eq2' : -2 * z.im * x + 1 = 0 := by linarith
      have : z.im = 1 / (2 * x) := by
        have h2ne : (2 * x : ℝ) ≠ 0 := by
          intro h
          apply h1
          linarith
        field_simp
        <;> nlinarith
      assumption
    have h3 : z.re = (x^2 + 3 / 4) / (2 * x) := by
      have hne : x ≠ 0 := h1
      have eq1' : x^2 - 2 * z.re * x + 3 / 4 = 0 := by linarith
      have : z.re = (x^2 + 3 / 4) / (2 * x) := by
        have h2ne : (2 * x : ℝ) ≠ 0 := by
          intro h
          apply h1
          linarith
        field_simp
        <;> nlinarith
      assumption
    have h4 : Complex.abs z = Real.sqrt ((z.re)^2 + (z.im)^2) := by
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf <;> simp [Complex.normSq]
      <;> ring_nf
    rw [h4] at hS
    have h5 : (z.re)^2 + (z.im)^2 ≥ 1 := by
      rw [h2, h3]
      have hne : x ≠ 0 := h1
      have hx2_pos : x ^ 2 > 0 := by
        apply pow_two_pos_of_ne_zero
        assumption
      have h6 : ((x ^ 2 + 3 / 4) / (2 * x)) ^ 2 + (1 / (2 * x)) ^ 2 ≥ 1 := by
        have h7 : ((x ^ 2 + 3 / 4) / (2 * x)) ^ 2 + (1 / (2 * x)) ^ 2 - 1 ≥ 0 := by
          have h8 : ((x ^ 2 + 3 / 4) / (2 * x)) ^ 2 + (1 / (2 * x)) ^ 2 - 1 =
              ((x ^ 2 + 3 / 4) ^ 2 + (1) ^ 2 - (2 * x) ^ 2) / ( (2 * x) ^ 2 ) := by
            field_simp
            <;> ring_nf <;> field_simp <;> ring_nf
            <;> ring_nf <;> field_simp
            <;> ring_nf
          rw [h8]
          have hx2_pos' : (2 * x) ^ 2 > 0 := by
            apply pow_two_pos_of_ne_zero
            by_contra h
            have : x = 0 := by
              linarith
            tauto
          have h9 : (x ^ 2 + 3 / 4) ^ 2 + (1) ^ 2 - (2 * x) ^ 2 ≥ 0 := by
            nlinarith [sq_nonneg (x ^ 2 - 5 / 4), sq_nonneg (x * Real.sqrt 5 - Real.sqrt 5 / 2 * Real.sqrt 5), sq_nonneg (x * Real.sqrt 5 + Real.sqrt 5 / 2 * Real.sqrt 5), Real.sqrt_pos.mpr (show (5: ℝ) > 0 by norm_num), Real.sq_sqrt (show (0: ℝ) ≤ (5: ℝ) by norm_num), sq_nonneg (x ^ 2), sq_nonneg (x * 1)]
          apply div_nonneg
          · linarith
          · nlinarith
        linarith
      linarith
    have h7 : Real.sqrt ((z.re)^2 + (z.im)^2) ≥ 1 := by
      have h8 : (z.re)^2 + (z.im)^2 ≥ 1 := h5
      have h9 : Real.sqrt ((z.re) ^ 2 + (z.im) ^ 2) ≥ Real.sqrt (1 : ℝ) := Real.sqrt_le_sqrt (h8)
      have h10 : Real.sqrt (1 : ℝ) = 1 := Real.sqrt_one
      linarith
      all_goals norm_num
    linarith [Real.sqrt_nonneg ((z.re) ^ 2 + (z.im) ^ 2)]