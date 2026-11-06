import Mathlib

open Polynomial

theorem algebra_16733 (p : ℝ[X]) (hpdegree : p.natDegree = 2) (hcoeff : p.coeff 1 = -4)
    (hroot : -2 - 3 * .I ∈ p.aroots ℂ) :
    p = C (-1) * X ^ 2 + C (-4) * X + C (-13) := by
  have eq1 : p.eval₂ (algebraMap ℝ ℂ) (-2 - 3 * Complex.I) = 0 := by
    have h1 := hroot
    simp [Polynomial.mem_aroots] at h1 ⊢
    norm_num at h1 ⊢
    try { tauto }
  have eq2 : p.eval₂ (algebraMap ℝ ℂ) (-2 - 3 * Complex.I) =
      (p.coeff 2) * (-2 - 3 * Complex.I) ^ 2 + (p.coeff 1) * (-2 - 3 * Complex.I) + (p.coeff 0) := by
    have eq3 : p.eval₂ (algebraMap ℝ ℂ) (-2 - 3 * Complex.I) = (p.coeff 2) * (-2 - 3 * Complex.I) ^ 2 + (p.coeff 1) * (-2 - 3 * Complex.I) + (p.coeff 0) := by 
      rw [Polynomial.eval₂_eq_sum_range]
      simp [hpdegree, Finset.sum_range_succ]
      <;> ring_nf
    simpa using eq3
  rw [eq2] at eq1 
  have eq3 : (p.coeff 2 : ℝ) * (-2 - 3 * Complex.I) ^ 2 + (p.coeff 1 : ℝ) * (-2 - 3 * Complex.I) + (p.coeff 0 : ℝ) = (0 : ℂ) := by 
    simpa using eq1
  have eq4 : (p.coeff 2 : ℝ) = -1 := by
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
          Complex.ofReal_re, Complex.ofReal_im] at eq3
    ring_nf at eq3 
    have h1c : (p.coeff 1: ℝ) = -4 := by
      simpa using hcoeff
    nlinarith [eq3.1, eq3.2, h1c]
  have eq5 : (p.coeff 0 : ℝ) = -13 := by 
    simp [pow_two, Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, 
          Complex.ofReal_re, Complex.ofReal_im] at eq3
    ring_nf at eq3 
    have h1c : (p.coeff 1: ℝ) = -4 := by
      simpa using hcoeff
    nlinarith [eq3.1, eq3.2, h1c]
  have eq9 : p = C (p.coeff 2) * X ^ 2 + C (p.coeff 1) * X + C (p.coeff 0) := by 
    apply Polynomial.funext
    intro x
    have eq6 : p.eval x = (p.coeff 2) * x ^ 2 + (p.coeff 1) * x + (p.coeff 0) := by 
      rw [Polynomial.eval_eq_sum_range' (show p.natDegree < (p.natDegree + 1) by omega)]
      simp [hpdegree, Finset.sum_range_succ]
      <;> ring_nf 
    simp [eq6, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_X]
  rw [eq9]
  simp [eq4, hcoeff, eq5]
  <;> ring_nf