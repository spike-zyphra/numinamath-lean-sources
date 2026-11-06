import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

/- [ Inequalities with vectors ]

Prove that from five vectors, it is always possible to choose two such that the length of their sum does not exceed the length of the sum of the remaining three vectors.

# -/
theorem inequalities_100916 (v : Fin 5 → EuclideanSpace ℝ (Fin 2)) :
    ∃ i j, i ≠ j ∧ ‖v i + v j‖ ≤ ‖v 0 + v 1 + v 2 + v 3 + v 4 - v i - v j‖ := by
  -- Use contradiction
  by_contra! h
  -- Specialize h to every pair of indices i and j
  have h01 : _ := h 0 1
  have h02 : _ := h 0 2
  have h03 : _ := h 0 3
  have h04 : _ := h 0 4
  have h12 : _ := h 1 2
  have h13 : _ := h 1 3
  have h14 : _ := h 1 4
  have h23 : _ := h 2 3
  have h24 : _ := h 2 4
  have h34 : _ := h 3 4
  -- Simplify every single hypothesis
  simp at *
  conv at h01 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h02 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h03 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h04 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h12 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h13 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h14 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h23 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h24 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  conv at h34 =>
    abel
    rw [← sq_lt_sq₀ (by positivity) (by positivity)]
    repeat rw [norm_add_sq_real]
    rw [inner_add_right]
  -- Add all the hypotheses together
  have : _ := add_lt_add h01 h02
  have : _ := add_lt_add h03 this
  have : _ := add_lt_add h04 this
  have : _ := add_lt_add h12 this
  have : _ := add_lt_add h13 this
  have : _ := add_lt_add h14 this
  have : _ := add_lt_add h23 this
  have : _ := add_lt_add h24 this
  have : _ := add_lt_add h34 this
  -- This implies the norm is negative
  have : 0 > ‖v 0 + v 1 + v 2 + v 3 + v 4‖ ^ 2 := by
    simp only [norm_add_sq_real, inner_add_left]
    linarith
  -- But the norm is always nonnegative
  have : ‖v 0 + v 1 + v 2 + v 3 + v 4‖ ^ 2 ≥ 0 := by positivity
  -- We have a contradiction
  linarith