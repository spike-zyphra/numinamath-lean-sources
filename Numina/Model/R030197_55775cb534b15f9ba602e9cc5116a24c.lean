import Mathlib

theorem algebra_21287 : ∑ i ∈ Finset.range 259, (Complex.I : ℂ) ^ (i + 1) = -1 := by
  have h1 : ∀ n, ∑ i in Finset.range n, (Complex.I : ℂ) ^ (i + 1) =
      (Complex.I - Complex.I ^ (n + 1)) / (1 - Complex.I) := by 
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      field_simp [sub_ne_zero, Complex.ext_iff, Complex.I_mul_I]
      <;> ring_nf <;> simp [Complex.I_sq] <;> ring
  have h2 : ∑ i in Finset.range 259, (Complex.I : ℂ) ^ (i + 1) = (Complex.I - Complex.I ^ 260) / (1 - Complex.I) := by 
    rw [h1 259]
    <;> ring_nf
  have h3 : Complex.I ^ 260 = 1 := by
    have h4 : Complex.I ^ 4 = 1 := by
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    calc
      Complex.I ^ 260 = Complex.I ^ (4 * 65) := by ring_nf
      _ = (Complex.I ^ 4) ^ 65 := by rw [pow_mul]
      _ = 1 ^ 65 := by rw [h4]
      _ = 1 := by norm_num
  rw [h2]
  rw [h3]
  have h4 : (Complex.I - (1 : ℂ)) / (1 - Complex.I) = -1 := by
    have h5 : (1 - Complex.I) ≠ 0 := by
      norm_num [Complex.ext_iff, Complex.I_mul_I]
    field_simp [h5, Complex.ext_iff, Complex.I_mul_I]
  rw [h4]