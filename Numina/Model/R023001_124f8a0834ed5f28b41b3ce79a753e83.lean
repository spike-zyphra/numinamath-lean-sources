import Mathlib

theorem algebra_217830 (z1 z2 : ℂ) (h₀ : Complex.abs z1 = 4) (h₁ : 4 * z1 ^ 2 - 2 * z1 * z2 + z2 ^ 2 = 0) :
    (1 / 2) * Complex.abs (z1 - z2) * Complex.abs z1 = 8 * Real.sqrt 3 := by
  have h2 : z2 ^ 2 - 2 * z1 * z2 + 4 * z1 ^ 2 = 0 := by
    calc
      z2 ^ 2 - 2 * z1 * z2 + 4 * z1 ^ 2 = (4 * z1 ^ 2 - 2 * z1 * z2 + z2 ^ 2) := by ring_nf
      _ = 0 := h₁
  have h3 : z2 = z1 * (1 + Complex.I * Real.sqrt 3) ∨ z2 = z1 * (1 + Complex.I * (-Real.sqrt 3)) := by
    have h4 : z2 ^ 2 - 2 * z1 * z2 + 4 * z1 ^ 2 = (z2 - z1 * (1 + Complex.I * Real.sqrt 3)) * (z2 - z1 * (1 + Complex.I * (-Real.sqrt 3))) := by
      ring_nf
      <;> simp [Complex.ext_iff, Complex.I_mul_I, pow_two, Complex.I_sq, Real.sq_sqrt]
      <;> ring_nf
      <;> norm_num [Real.sq_sqrt, Complex.I_sq]
      <;> ring_nf
      <;> field_simp [Complex.ext_iff, Complex.I_mul_I, pow_two]
      <;> ring_nf
      <;> field_simp [Complex.ext_iff, Complex.I_mul_I, pow_two]
      <;> ring_nf
      <;> norm_num [Real.sq_sqrt, Complex.I_sq]
    rw [h4] at h2
    cases (mul_eq_zero.mp h2) with
    | inl h5 =>
      left
      have h6 : z2 = z1 * (1 + Complex.I * Real.sqrt 3) := by
        have h7 : z2 - z1 * (1 + Complex.I * Real.sqrt 3) = 0 := h5
        have h8 : z2 = z1 * (1 + Complex.I * Real.sqrt 3) := by
          calc
            z2 = z2 - z1 * (1 + Complex.I * Real.sqrt 3) + z1 * (1 + Complex.I * Real.sqrt 3) := by ring_nf
            _ = 0 + z1 * (1 + Complex.I * Real.sqrt 3) := by rw [h7]
            _ = z1 * (1 + Complex.I * Real.sqrt 3) := by ring_nf
        exact h8
      exact h6
    | inr h6 =>
      right
      have h7 : z2 = z1 * (1 + Complex.I * (-Real.sqrt 3)) := by
        have h8 : z2 - z1 * (1 + Complex.I * (-Real.sqrt 3)) = 0 := h6
        have h9 : z2 = z1 * (1 + Complex.I * (-Real.sqrt 3)) := by
          calc
            z2 = z2 - z1 * (1 + Complex.I * (-Real.sqrt 3)) + z1 * (1 + Complex.I * (-Real.sqrt 3)) := by ring_nf
            _ = 0 + z1 * (1 + Complex.I * (-Real.sqrt 3)) := by rw [h8]
            _ = z1 * (1 + Complex.I * (-Real.sqrt 3)) := by ring_nf
        exact h9
      exact h7
  cases h3 with
  | inl h3 =>
    have eq1 : z2 = z1 * (1 + Complex.I * Real.sqrt 3) := h3
    have eq2 : z1 - z2 = z1 * (-Complex.I * Real.sqrt 3) := by
      rw [eq1]
      ring_nf
      <;> simp [Complex.ext_iff, mul_add, pow_two, Complex.I_sq, Real.sq_sqrt]
      <;> ring_nf
      <;> field_simp [Complex.ext_iff, Complex.I_mul_I]
      <;> ring_nf
      <;> norm_num
    rw [eq2]
    have h4 : Complex.abs (z1 * (-Complex.I * Real.sqrt 3)) = Complex.abs z1 * Complex.abs (-Complex.I * Real.sqrt 3) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> norm_num
    rw [h4, h₀]
    have h5 : Complex.abs (-Complex.I * Real.sqrt 3) = Real.sqrt 3 := by
      simp [Complex.abs, Complex.normSq, Complex.I_mul_I, pow_two]
      <;> ring_nf
      <;> norm_num [Real.sq_sqrt, Complex.I_sq]
      all_goals ring_nf
    rw [h5]
    <;> ring_nf
    all_goals norm_num [Real.sq_sqrt, Complex.I_sq]
    <;> ring_nf <;> norm_num <;> ring_nf
  | inr h3 =>
    have eq1 : z2 = z1 * (1 + Complex.I * (-Real.sqrt 3)) := h3
    have eq2 : z1 - z2 = z1 * (Complex.I * Real.sqrt 3) := by
      rw [eq1]
      ring_nf
      <;> simp [Complex.ext_iff, mul_add, pow_two, Complex.I_sq, Real.sq_sqrt]
      <;> ring_nf
      <;> field_simp [Complex.ext_iff, Complex.I_mul_I, pow_two]
      <;> ring_nf
      <;> norm_num
      <;> ring_nf
    rw [eq2]
    have h4 : Complex.abs (z1 * (Complex.I * Real.sqrt 3)) = Complex.abs z1 * Complex.abs (Complex.I * Real.sqrt 3) := by 
      simp [Complex.abs, Complex.normSq]
      <;> ring_nf
      <;> norm_num
    rw [h4, h₀]
    have h5 : Complex.abs (Complex.I * Real.sqrt 3) = Real.sqrt 3 := by
      simp [Complex.abs, Complex.normSq, Complex.I_mul_I, pow_two]
      <;> ring_nf
      <;> norm_num [Real.sq_sqrt, Complex.I_sq]
      all_goals ring_nf
    rw [h5]
    <;> ring_nf
    all_goals norm_num [Real.sq_sqrt, Complex.I_sq]
    <;> ring_nf <;> norm_num <;> ring_nf