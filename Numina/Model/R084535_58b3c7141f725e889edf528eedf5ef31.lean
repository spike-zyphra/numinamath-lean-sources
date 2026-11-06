import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_205531 (x : Fin 5 → ℝ)
  (h₀ : ∀ i, 0 ≤ x i)
  (h₁ : ∑ i, x i = 300)
  (M : ℝ)
  (hM : M = max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4)) :
  M ≥ 100 := by
  have h2 : 0 ≤ x 0 := h₀ 0
  have h3 : 0 ≤ x 1 := h₀ 1
  have h4 : 0 ≤ x 2 := h₀ 2
  have h5 : 0 ≤ x 3 := h₀ 3
  have h6 : 0 ≤ x 4 := h₀ 4
  have h7 : x 0 + x 1 + x 2 + x 3 + x 4 = 300 := by
    have h8 : ∑ i, x i = x 0 + x 1 + x 2 + x 3 + x 4 := by
      simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ]
      all_goals try simp_all
      all_goals norm_num
    rw [h8] at h₁
    linarith
  rw [hM]
  by_contra h
  push_neg at h
  have h8 : x 0 + x 1 < 100 := by
    have h9 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) < 100 := by
      simpa using h
    have h10 : x 0 + x 1 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) := by
      simp
    linarith
  have h9 : x 1 + x 2 < 100 := by
    have h10 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) < 100 := by
      simpa using h
    have h11 : x 1 + x 2 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) := by
      simp
    linarith
  have h10 : x 2 + x 3 < 100 := by
    have h11 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) < 100 := by
      simpa using h
    have h12 : x 2 + x 3 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) := by
      simp
    linarith
  have h11 : x 3 + x 4 < 100 := by
    have h12 : max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) < 100 := by
      simpa using h
    have h13 : x 3 + x 4 ≤ max (max (max (x 0 + x 1) (x 1 + x 2)) (x 2 + x 3)) (x 3 + x 4) := by
      simp
    linarith
  nlinarith