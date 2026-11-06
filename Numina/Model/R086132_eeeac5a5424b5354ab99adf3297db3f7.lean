import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_156138 (f : ℝ → ℝ) (hf : f = λ x => x + cos (2 * x)) :
    ∃ x ∈ Ioo 0 (π / 4), f x = π / 12 + sqrt 3 / 2 := by
  use π / 12
  constructor
  · -- Show that π/12 is in the interval (0, π/4)
    constructor
    · -- Show π/12 > 0
      linarith [Real.pi_pos]
    · -- Show π/12 < π/4
      linarith [Real.pi_pos]
  · -- Show f(π/12) = π/12 + sqrt(3)/2
    rw [hf]
    have h1 : cos (2 * (π / 12)) = sqrt 3 / 2 := by
      have h2 : 2 * (π / 12) = π / 6 := by ring
      rw [h2]
      have h3 : cos (π / 6) = sqrt 3 / 2 := by
        exact cos_pi_div_six
      rw [h3]
    simp [h1]
    <;> ring_nf <;> field_simp [Real.pi_pos]
    <;> linarith [Real.pi_pos]