import Mathlib

open Complex Polynomial Real

theorem algebra_95191 : ∃ (P : Polynomial ℂ), P.degree = 4 ∧ Monic P ∧ (∃ x y : ℤ, x ≠ y ∧ P.eval (x : ℂ) = 0 ∧ P.eval (y : ℂ) = 0) ∧ P.eval ((1 + Complex.I * Real.sqrt 11) / 2) = 0 := by
  use (X ^ 4 - 2 * X ^ 3 + 4 * X ^ 2 - 3 * X)
  constructor
  · -- Compute the degree of the polynomial
    compute_degree!
    <;> norm_num
  constructor
  · -- Show that the polynomial is monic
    monicity!
  constructor
  · -- Show that there are two distinct integer roots
    use 1, 0
    constructor
    · -- Show that 1 ≠ 0
      norm_num
    constructor
    · -- Show that P(1) = 0
      simp [pow_two, pow_succ, Complex.ext_iff]
      <;> norm_num
    · -- Show that P(0) = 0
      simp [pow_two, pow_succ, Complex.ext_iff]
      <;> norm_num
  · -- Show that (1 + i * sqrt 11)/2 is a root of the polynomial
    simp [pow_two, pow_succ, Complex.ext_iff]
    field_simp
    <;> ring_nf <;> norm_num [Real.sqrt_sq]
    <;> nlinarith [Real.sqrt_pos.mpr (show 0 < (11 : ℝ) by norm_num), Real.sq_sqrt (show 0 ≤ (11 : ℝ) by norm_num)]