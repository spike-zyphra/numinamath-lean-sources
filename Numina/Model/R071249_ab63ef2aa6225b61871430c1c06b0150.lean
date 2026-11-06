import Mathlib

open Set Real

theorem inequalities_119358 (A B : Set ℝ) (hA : A = {x | x^2 - 3 * x - 10 ≤ 0})
    (hB : B = {x | m + 1 ≤ x ∧ x ≤ 2 * m - 1}) (hAB : A ∩ B = B) :
    m ≤ 3 := by 
  have h1 : B ⊆ A := by 
    rw [Set.inter_eq_right] at hAB 
    exact hAB 
  rw [hB] at h1 
  rw [hA] at h1 
  by_contra h 
  push_neg at h 
  have h2 : m + 1 ≤ 2 * m - 1 := by linarith 
  have h3 : 2 * m - 1 ∈ ({x | m + 1 ≤ x ∧ x ≤ 2 * m - 1}) := by 
    constructor 
    · linarith 
    · linarith 
  have h4 : 2 * m - 1 ∈ ({x | x ^ 2 - 3 * x - 10 ≤ 0}) := h1 h3 
  simp at h4 
  nlinarith [h]