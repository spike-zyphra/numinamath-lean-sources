import Mathlib

open Real Complex Polynomial

theorem algebra_252696 {f : ℕ → ℂ} (hf : ∀ n, f n = ((1 + I) / sqrt 2)^n + ((1 - I) / sqrt 2)^n) :
    f 1986 + f 1990 = 0 := by
  have eq1 : f 1986 = ((1 + I) / sqrt 2) ^ 1986 + ((1 - I) / sqrt 2) ^ 1986 := hf 1986
  have eq2 : f 1990 = ((1 + I) / sqrt 2) ^ 1990 + ((1 - I) / sqrt 2) ^ 1990 := hf 1990
  rw [eq1, eq2]
  have h1 : ((1 + I) / sqrt 2) ^ 2 = I := by 
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_add, mul_sub, sq, div_pow, Real.sqrt_sq]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    <;> try linarith
    <;> try ring_nf
    <;> try norm_num
    <;> try tauto
  have h2 : ((1 - I) / sqrt 2) ^ 2 = -I := by 
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_add, mul_sub, sq, div_pow, Real.sqrt_sq]
    <;> ring_nf <;> norm_num
    <;> ring_nf <;> norm_num
    <;> try linarith
    <;> try ring_nf
    <;> try norm_num
    <;> try tauto
  have eq3 : ((1 + I) / sqrt 2) ^ 1986 = ((1 + I) / sqrt 2) ^ (2 * 993) := by 
    norm_num
  have eq4 : ((1 + I) / sqrt 2) ^ (2 * 993) = (((1 + I) / sqrt 2) ^ 2) ^ 993 := by 
    rw [pow_mul]
  have eq5 : ((1 - I) / sqrt 2) ^ 1986 = ((1 - I) / sqrt 2) ^ (2 * 993) := by 
    norm_num
  have eq6 : ((1 - I) / sqrt 2) ^ (2 * 993) = (((1 - I) / sqrt 2) ^ 2) ^ 993 := by 
    rw [pow_mul]
  have eq7 : ((1 + I) / sqrt 2) ^ 1990 = ((1 + I) / sqrt 2) ^ (2 * 995) := by 
    norm_num
  have eq8 : ((1 + I) / sqrt 2) ^ (2 * 995) = (((1 + I) / sqrt 2) ^ 2) ^ 995 := by 
    rw [pow_mul]
  have eq9 : ((1 - I) / sqrt 2) ^ 1990 = ((1 - I) / sqrt 2) ^ (2 * 995) := by 
    norm_num
  have eq10 : ((1 - I) / sqrt 2) ^ (2 * 995) = (((1 - I) / sqrt 2) ^ 2) ^ 995 := by 
    rw [pow_mul]
  rw [eq3, eq4, h1, eq5, eq6, h2, eq7, eq8, h1, eq9, eq10, h2]
  have eq13 : (-I : ℂ) ^ 993 = (-1 : ℂ) ^ 993 * I ^ 993 := by 
    have h_eq : (-I : ℂ) = (-1 : ℂ) * I := by 
      simp [Complex.ext_iff, mul_one]
      <;> norm_num [Complex.ext_iff]
      <;> try ring_nf
    rw [h_eq]
    rw [mul_pow]
  have eq14 : (-I : ℂ) ^ 995 = (-1 : ℂ) ^ 995 * I ^ 995 := by 
    have h_eq : (-I : ℂ) = (-1 : ℂ) * I := by 
      simp [Complex.ext_iff, mul_one]
      <;> norm_num [Complex.ext_iff]
      <;> try ring_nf
    rw [h_eq]
    rw [mul_pow]
  have h3 : (-1 : ℂ) ^ 993 = -1 := by 
    norm_num [pow_succ, pow_zero]
  have h4 : (-1 : ℂ) ^ 995 = -1 := by 
    norm_num [pow_succ, pow_zero]
  simp [eq13, h3, eq14, h4]
  <;> ring_nf <;> norm_num
  <;> try ring_nf
  <;> try simp [pow_succ, pow_zero]
  <;> try norm_num
  <;> try tauto