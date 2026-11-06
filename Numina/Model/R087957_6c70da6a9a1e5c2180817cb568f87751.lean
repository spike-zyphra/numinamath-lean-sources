import Mathlib

open Complex Filter Function Metric Finset
open scoped BigOperators Topology

theorem algebra_251911 {A : ℂ} (hA : A = (1 + (1 + I) / 2) * (1 + ((1 + I) / 2)^2) *
  (1 + ((1 + I) / 2)^4) * (1 + ((1 + I) / 2)^8)) :
  A = 255 / 256 * (1 + I) := by
    rw [hA]
    field_simp [Complex.ext_iff, pow_two, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    <;> norm_num [Complex.ext_iff]
    all_goals norm_num
    all_goals field_simp [Complex.ext_iff, pow_two, pow_succ, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
    <;> norm_num [Complex.ext_iff]