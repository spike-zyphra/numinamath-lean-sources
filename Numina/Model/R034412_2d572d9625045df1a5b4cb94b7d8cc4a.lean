import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_138588 (f : ℝ → ℝ) (hf : f = λ x => sin x)
  (a b : ℝ) (ha : a = 0) (hb : b = π) :
  ∫ x in (a)..b, π * (f x)^2 = (π^2)/2 := by
  rw [hf, ha, hb]
  simp [mul_comm]
  ring_nf
  <;> field_simp
  <;> ring_nf