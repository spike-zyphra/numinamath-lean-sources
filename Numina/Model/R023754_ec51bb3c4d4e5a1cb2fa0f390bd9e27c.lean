import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_225599 (α : ℝ) (h : sin α ≠ 0) (n : ℕ) :
  ∏ k ∈ Finset.range (n + 1), cos (2 ^ k * α) = sin (2 ^ (n + 1) * α) / (2 ^ (n + 1) * sin α) := by
  induction n with
  | zero =>
    simp
    have h2 : sin (2 * α) = 2 * sin α * cos α := by
      rw [sin_two_mul]
    rw [h2]
    field_simp [h]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    have h2 : sin (2 ^ (n + 2) * α) = 2 * sin (2 ^ (n + 1) * α) * cos (2 ^ (n + 1) * α) := by
      have h3 : 2 ^ (n + 2) * α = 2 * (2 ^ (n + 1) * α) := by
        ring_nf
      rw [h3]
      rw [sin_two_mul]
    rw [h2]
    field_simp [h]
    ring_nf