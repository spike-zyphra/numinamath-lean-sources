import Mathlib

theorem algebra_13344 : ∑ i ∈ Finset.range 2010, (Complex.I : ℂ)^i = 1 + Complex.I := by
  have h2 : ∑ i in Finset.range 2010, (Complex.I : ℂ) ^ i = (1 - Complex.I ^ 2010) / (1 - Complex.I) := by
    have h3 : ∀ (n : ℕ), ∑ i in Finset.range n, (Complex.I : ℂ) ^ i = (1 - Complex.I ^ n) / (1 - Complex.I) := by 
      intro n
      induction n with 
      | zero => 
        simp
      | succ n ih =>
        rw [Finset.sum_range_succ, ih]
        field_simp [sub_ne_zero, Complex.ext_iff, Complex.I_mul_I]
        <;> ring_nf <;> simp [Complex.I_sq] <;> ring
    specialize h3 2010
    simpa using h3
  have h3 : Complex.I ^ 2010 = -1 := by
    have h4 : Complex.I ^ 4 = 1 := by
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    calc
      Complex.I ^ 2010 = Complex.I ^ (4 * 502 + 2) := by norm_num
      _ = (Complex.I ^ 4) ^ 502 * Complex.I ^ 2 := by ring
      _ = (1) ^ 502 * Complex.I ^ 2 := by rw [h4]
      _ = Complex.I ^ 2 := by ring
      _ = -1 := by
        simp [Complex.I_sq]
  rw [h2, h3]
  field_simp [sub_ne_zero, Complex.ext_iff, Complex.I_mul_I]
  <;> norm_num