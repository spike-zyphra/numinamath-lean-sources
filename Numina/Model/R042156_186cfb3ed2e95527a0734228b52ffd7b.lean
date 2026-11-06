import Mathlib

theorem algebra_14450 : ∑ I ∈ Finset.range 601, (Complex.I : ℂ)^I = 1 := by
  have h1 : ∀ n, ∑ I in Finset.range n, (Complex.I : ℂ) ^ I = (1 - Complex.I ^ n) / (1 - Complex.I) := by
    intro n 
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [sub_ne_zero, Complex.ext_iff, Complex.I_mul_I]
      <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have h2 : ∑ I in Finset.range 601, (Complex.I : ℂ) ^ I = (1 - Complex.I ^ 601) / (1 - Complex.I) := h1 601
  rw [h2]
  have h3 : Complex.I ^ 601 = Complex.I := by
    have h4 : Complex.I ^ 4 = 1 := by
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    calc 
      Complex.I ^ 601 = Complex.I ^ (4 * 150 + 1) := by ring_nf
      _ = (Complex.I ^ 4) ^ 150 * Complex.I := by ring 
      _ = (1) ^ 150 * Complex.I := by rw [h4]
      _ = 1 * Complex.I := by ring
      _ = Complex.I := by ring 
  rw [h3]
  field_simp [sub_ne_zero, Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num [Complex.ext_iff, pow_two, Complex.I_mul_I]