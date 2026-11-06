import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_307986 {z1 z2 : ℂ} :
  (z1 * (z2.1 - z2.2 * I) + (z1.1 - z1.2 * I) * z2) = 0 ↔
  (z1.re * z2.re + z1.im * z2.im) = 0 := by
  simp [Complex.ext_iff, Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
        Complex.I_re, Complex.I_im]
  <;> ring_nf <;> norm_num <;> ring_nf <;> norm_num
  <;> ring