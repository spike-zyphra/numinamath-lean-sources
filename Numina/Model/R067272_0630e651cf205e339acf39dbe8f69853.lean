import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_186740 (x : Fin 5 → ℝ)
  (h₀ : ∀ i, 0 ≤ x i)
  (h₁ : ∑ i, x i = 1) :
  max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) ≥ 1 / 3 := by
  simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h₁
  have h3 : x 0 ≥ 0 := h₀ 0
  have h4 : x 1 ≥ 0 := h₀ 1
  have h5 : x 2 ≥ 0 := h₀ 2
  have h6 : x 3 ≥ 0 := h₀ 3
  have h7 : x 4 ≥ 0 := h₀ 4
  by_contra h
  push_neg at h
  -- Now max ... < 1/3 from the previous negation. Let's derive an inequality.
  have h8 : x 0 + x 1 < 1 / 3 := by
    have h21 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) < 1 / 3 := by linarith
    have h81 : x 0 + x 1 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) := by
      simp
    linarith
  have h9 : x 1 + x 2 < 1 / 3 := by
    have h21 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) < 1 / 3 := by linarith
    have h82 : x 1 + x 2 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) := by
      simp
    linarith
  have h10 : x 2 + x 0 < 1 / 3 := by
    have h21 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) < 1 / 3 := by linarith
    have h83 : x 2 + x 0 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) := by
      simp
    linarith
  have h11 : x 3 + x 4 < 1 / 3 := by
    have h21 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) < 1 / 3 := by linarith
    have h84 : x 3 + x 4 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 0)) (x 3 + x 4) := by
      simp
    linarith
  -- Now variables have bound.
  linarith [h₁, h8, h9, h10, h11]