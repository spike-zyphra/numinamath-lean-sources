import Mathlib

open Real Complex Polynomial LinearMap FiniteDimensional Module Module.End
open scoped BigOperators

theorem other_184462 (R Q ω : ℝ) (hR : R > 0) (hQ : Q > 0)
  (hω : ω > 0) :
  let B := λ θ => (Q * ω) / (2 * π * R * (1 + Real.cos θ) ^ 2)
  B 0 = (Q * ω) / (8 * π * R) := by
  intro B
  simp [B, Real.cos_zero]
  <;> ring_nf