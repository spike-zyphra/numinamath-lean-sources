import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_59841 (r h : ℝ) (hr : r > 0) (hh : h > 0) :
    ∫ x in (0)..h, π * (r ^ 2) = π * r ^ 2 * h := by 
  simp [intervalIntegral.integral_const, mul_comm]
  <;> ring_nf <;> field_simp <;> ring