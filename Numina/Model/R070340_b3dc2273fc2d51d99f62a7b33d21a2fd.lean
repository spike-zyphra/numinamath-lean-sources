import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_108877 (a : ℝ) (A B : Set ℝ)
  (hA : A = {x | 1 ≤ x ∧ x ≤ 2}) (hB : B = {x | x^2 - a * x + 4 ≥ 0}) :
  A ⊆ B ↔ a ≤ 4 := by
  constructor
  · -- Forward direction: assume A ⊆ B, prove a ≤ 4
    intro h
    have h2 : 2 ∈ A := by
      rw [hA]
      exact ⟨by norm_num, by norm_num⟩
    have h3 : 2 ∈ B := h h2
    rw [hB] at h3
    simp at h3
    linarith
  · -- Backward direction: assume a ≤ 4, prove A ⊆ B
    intro ha x hx
    rw [hA] at hx
    have hx1 : 1 ≤ x := hx.1
    have hx2 : x ≤ 2 := hx.2
    rw [hB]
    simp
    have h1 : x ≥ 1 := by linarith
    have h2 : x ≤ 2 := by linarith
    have h3 : x ^ 2 - a * x + 4 ≥ 0 := by
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - a / 2), sq_nonneg (a - 4), sq_nonneg (x - 1)]
    linarith