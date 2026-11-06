import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_245548 {z : ℂ} (hz : (z - 1)^2 = abs (z - 1)^2) :
    z.im = 0 := by
  have eq2 := congr_arg Complex.im hz
  simp [pow_two, Complex.add_im, Complex.mul_im, Complex.abs, Complex.normSq] at eq2
  have eq3 : z.im * (z.re - 1) = 0 := by
    ring_nf at eq2 ⊢
    nlinarith
  cases' (mul_eq_zero.mp eq3) with h1 h2
  · -- Case where h1 holds, i.e., z.im = 0
    simpa using h1
  · -- Case where h2 holds, i.e., z.re - 1 = 0
    have eq4 : z.re = 1 := by linarith
    have eq5 := congr_arg Complex.re hz
    simp [pow_two, Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.abs, Complex.normSq, eq4] at eq5
    nlinarith [sq_nonneg (z.im)]