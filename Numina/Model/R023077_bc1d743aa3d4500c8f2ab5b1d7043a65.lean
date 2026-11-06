import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_313043 {i : ℂ} (hi : i = I) :
    (∑ j ∈ range 2014, i ^ j) * (∑ j ∈ range 2014, (-i) ^ j) = 2 := by
  rw [hi]
  have h1 : ∀ n, ∑ j in range n, Complex.I ^ j = (1 - Complex.I ^ n) / (1 - Complex.I) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp [Complex.ext_iff, Complex.I_mul_I]
      ring_nf
      <;> simp [Complex.I_mul_I, pow_succ]
      all_goals ring

  have h2 : ∀ n, ∑ j in range n, (-Complex.I : ℂ) ^ j = (1 - (-Complex.I : ℂ) ^ n) / (1 - (-Complex.I : ℂ)) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp [Complex.ext_iff, Complex.I_mul_I]
      ring_nf
      <;> simp [Complex.I_mul_I, pow_succ]
      all_goals ring

  have h3 : (∑ j in range 2014, Complex.I ^ j) = (1 - Complex.I ^ 2014) / (1 - Complex.I) := by 
    specialize h1 2014
    simpa using h1

  have h4 : (∑ j in range 2014, (-Complex.I : ℂ) ^ j) = (1 - (-Complex.I : ℂ) ^ 2014) / (1 - (-Complex.I : ℂ)) := by 
    specialize h2 2014
    simpa using h2

  have h5 : Complex.I ^ 2014 = -1 := by
    have h6 : Complex.I ^ 4 = 1 := by
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    calc
      Complex.I ^ 2014 = Complex.I ^ (4 * 503 + 2) := by norm_num
      _ = (Complex.I ^ 4) ^ 503 * Complex.I ^ 2 := by ring
      _ = 1 ^ 503 * Complex.I ^ 2 := by rw [h6]
      _ = Complex.I ^ 2 := by ring
      _ = -1 := by
        have h7 : Complex.I ^ 2 = -1 := by
          norm_num [Complex.ext_iff, Complex.I_mul_I]
        rw [h7]

  have h8 : (-Complex.I : ℂ) ^ 2014 = -1 := by
    have h9 : (-Complex.I : ℂ) ^ 4 = 1 := by
      norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
    calc
      (-Complex.I : ℂ) ^ 2014 = (-Complex.I : ℂ) ^ (4 * 503 + 2) := by norm_num
      _ = ((-Complex.I : ℂ) ^ 4) ^ 503 * (-Complex.I : ℂ) ^ 2 := by ring
      _ = 1 ^ 503 * (-Complex.I : ℂ) ^ 2 := by rw [h9]
      _ = (-Complex.I : ℂ) ^ 2 := by ring
      _ = -1 := by
        have h10 : (-Complex.I : ℂ) ^ 2 = -1 := by
          norm_num [pow_succ, Complex.ext_iff, Complex.I_mul_I]
        rw [h10]

  rw [h3, h4]
  rw [h5, h8]
  field_simp [Complex.ext_iff, Complex.I_mul_I]
  all_goals norm_num