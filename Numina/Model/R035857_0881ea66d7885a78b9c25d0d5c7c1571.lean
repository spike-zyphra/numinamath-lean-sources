import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_148563 : ∫ x in (-π)..0, sin x < 0 := by
  have h1 : ∫ x in (-π)..0, sin x = -2 := by
    simp [intervalIntegral.integral_const, sin_pi, cos_pi]
    <;> ring
  rw [h1]
  norm_num