import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_247194 {f : ℝ → ℝ}
  (hf : f = λ x => 2 * sin (3 / 4 * x) + cos (4 / 5 * x - π / 3)) :
  ∃ c, Function.Periodic f c ∧ c = 40 * π := by
  use 40 * π
  constructor
  · -- Show f is periodic with period 40 * π
    rw [hf]
    intro x
    have h1 : sin (3 / 4 * (x + 40 * π)) = sin (3 / 4 * x) := by
      have h3 : 3 / 4 * (x + 40 * π) = 3 / 4 * x + 30 * π := by
        ring_nf
      rw [h3]
      have h4 : sin (3 / 4 * x + 30 * π) = sin (3 / 4 * x) := by
        have h5 : sin (3 / 4 * x + 30 * π) = sin (3 / 4 * x + 15 * (2 * π)) := by
          ring_nf
        rw [h5]
        have h6 : sin (3 / 4 * x + 15 * (2 * π)) = sin (3 / 4 * x) := by
          have h7 : sin (3 / 4 * x + 15 * (2 * π)) = sin (3 / 4 * x + (15 : ℤ) * (2 * π)) := by
            ring_nf
          rw [h7]
          rw [Real.sin_add_int_mul_two_pi]
        exact h6
      exact h4
    have h2 : cos (4 / 5 * (x + 40 * π) - π / 3) = cos (4 / 5 * x - π / 3) := by
      have h3 : 4 / 5 * (x + 40 * π) - π / 3 = (4 / 5 * x - π / 3) + 32 * π := by
        ring_nf
      rw [h3]
      have h4 : cos ((4 / 5 * x - π / 3) + 32 * π) = cos (4 / 5 * x - π / 3) := by
        have h5 : cos ((4 / 5 * x - π / 3) + 32 * π) = cos (4 / 5 * x - π / 3 + (16 * (2 * π))) := by
          ring_nf
        rw [h5]
        have h6 : cos (4 / 5 * x - π / 3 + (16 * (2 * π))) = cos (4 / 5 * x - π / 3 + ((16 : ℤ) * (2 * π))) := by
          ring_nf
        rw [h6]
        rw [Real.cos_add_int_mul_two_pi]
      exact h4
    simp [h1, h2]
    <;> ring_nf <;> field_simp [Real.sin_sq_add_cos_sq]
    <;> ring_nf <;> field_simp [Real.sin_sq_add_cos_sq]
    <;> ring
  · -- Show c = 40 * π
    rfl