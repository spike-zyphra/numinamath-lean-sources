import Mathlib

open Polynomial

/-- Find a non-zero polynomial $P$ with integer coefficients such that 
  $P(\sqrt {2008} + \sqrt {2009}) = 0$.
-/
theorem algebra_4209 {p : ℝ[X]} : p = X^4 - 8034 * X^2 + 1 → p ≠ 0 ∧ p.eval (√2008 + √2009) = 0 := by
  intro h'
  rw [h']
  constructor
  -- Polynomial $P$ is non-zero.
  · have : 4 ∈ Polynomial.support (X ^ 4 - 8034 * X ^ 2 + 1 : ℝ[X]) := by
      simp [mem_support_iff]
      have : coeff (1 : ℝ[X]) 4 = 0 := by
        rw [Polynomial.coeff_one]
        simp
      rw [this]
      aesop
    have : _ := (Polynomial.le_degree_of_mem_supp 4) this
    apply Polynomial.ne_zero_of_coe_le_degree this
  -- Check the value of $x^4 -8034x^2 + 1$ at $\sqrt {2008} + \sqrt {2009}$ equal zero.
  · simp
    have : (1 : ℝ) = 4017^2 - 4 * 2008 * 2009 := by ring
    rw [this]
    suffices h : (√2008 + √2009) ^ 4 - 8034 * (√2008 + √2009) ^ 2 + 4017 ^ 2 = 4 * 2008 * 2009 by
      linarith
    suffices h : ((√2008 + √2009)^2 - 4017)^2 = 4 * 2008 * 2009 by
      linarith
    have : 4 * 2008 * 2009 = (2 * √2008 * √2009)^2 := by
      ring_nf; simp_all; ring_nf
    rw [this,sq_eq_sq_iff_eq_or_eq_neg]
    left
    suffices h : (√2008 + √2009) ^ 2 = √2008^2 + 2 * √2008 * √2009 + √2009^2 from by
      rw [h]; simp_all; ring_nf
    ring_nf
