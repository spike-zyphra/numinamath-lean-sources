import Mathlib

open Real Set
open scoped BigOperators

theorem calculus_22929 (f : ℝ → ℝ) (hf : f = λ x => cos x + cos (2 * x) + cos (3 * x)) :
    Function.Periodic f (2 * π) := by
  rw [hf]
  intro x
  have h1 : cos (x + 2 * π) = cos x := by
    rw [cos_add_two_pi]
  have h2 : cos (2 * (x + 2 * π)) = cos (2 * x) := by
    have h21 : 2 * (x + 2 * π) = 2 * x + 4 * π := by ring
    rw [h21]
    have h22 : cos (2 * x + 4 * π) = cos (2 * x) := by
      have h23 : cos (2 * x + 4 * π) = cos (2 * x + 2 * π + 2 * π) := by ring_nf
      rw [h23]
      have h24 : cos (2 * x + 2 * π + 2 * π) = cos (2 * x) := by
        rw [cos_add, cos_add]
        simp [cos_two_pi, sin_two_pi]
        <;> ring
      exact h24
    exact h22
  have h3 : cos (3 * (x + 2 * π)) = cos (3 * x) := by
    have h31 : 3 * (x + 2 * π) = 3 * x + 6 * π := by ring
    rw [h31]
    have h32 : cos (3 * x + 6 * π) = cos (3 * x) := by
      have h33 : cos (3 * x + 6 * π) = cos (3 * x + 3 * (2 * π)) := by ring_nf
      rw [h33]
      have h34 : cos (3 * x + 3 * (2 * π)) = cos (3 * x) := by
        have h36 : cos (3 * x + 3 * (2 * π)) = cos (3 * x) := by
          rw [show 3 * x + 3 * (2 * π) = (3 * x) + (3 : ℕ) * (2 * π) by ring]
          rw [cos_add_nat_mul_two_pi]
        exact h36
      exact h34
    exact h32
  simp [h1, h2, h3]
  <;> ring