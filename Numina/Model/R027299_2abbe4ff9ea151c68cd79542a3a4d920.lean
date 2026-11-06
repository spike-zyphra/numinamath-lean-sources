import Mathlib

open Finset Real

theorem inequalities_65258 {n : ℕ} (hn : 0 < n) (a : Fin (2 * n) → ℝ)
    (ha : ∀ i, 1 ≤ a i ∧ a i ≤ 2 * n) :
    ∃ s1 s2 : ℝ, s1 > 0 ∧ s2 > 0 ∧
      (∑ i : Fin (2 * n), a i = s1 + s2) ∧
      (n / (n + 1 : ℝ) ≤ s1 / s2 ∧ s1 / s2 ≤ 1) := by 
  use (∑ i : Fin (2 * n), a i) / 2, (∑ i : Fin (2 * n), a i) / 2
  have h2 : ∑ i : Fin (2 * n), a i > 0 := by
    have h3 : ∀ i : Fin (2 * n), a i ≥ 1 := by 
      intro i
      exact (ha i).left
    have h4 : ∑ i : Fin (2 * n), a i ≥ ∑ i : Fin (2 * n), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      specialize h3 i
      linarith
    have h5 : ∑ i : Fin (2 * n), (1 : ℝ) = (2 * n : ℝ) := by 
      simp
      <;> ring
    have h6 : ∑ i : Fin (2 * n), a i ≥ (2 * n : ℝ) := by
      linarith [h4, h5]
    have h7 : (2 * n : ℝ) > 0 := by
      have hn' : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 by linarith)
      nlinarith
    nlinarith
  constructor
  · -- Show s1 > 0
    nlinarith
  constructor
  · -- Show s2 > 0
    nlinarith
  constructor
  · -- Show ∑ i, a i = s1 + s2
    ring
  constructor
  · -- Show n / (n + 1) ≤ s1 / s2
    have h3 : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 by linarith)
    have h4 : (n + 1 : ℝ) > 0 := by
      have h4 : (n : ℝ) > 0 := h3
      nlinarith
    have h5 : (n / (n + 1 : ℝ) ) ≤ (1 : ℝ) := by
      have h6 : (n : ℝ) ≤ (n + 1 : ℝ) := by linarith
      have h7 : (n + 1 : ℝ) > 0 := h4
      apply (div_le_iff₀ (by positivity)).mpr
      nlinarith
    have h7 : (∑ i : Fin (2 * n), a i ) > 0 := h2
    have h8 : ( (∑ i : Fin (2 * n), a i) / 2 ) / ( (∑ i : Fin (2 * n), a i) / 2 ) = (1 : ℝ) := by
      have h7 : (∑ i : Fin (2 * n), a i ) > 0 := h2
      field_simp
      <;> ring
    nlinarith [h5, h8]
  · -- Show s1 / s2 ≤ 1
    have h2 : ∑ i : Fin (2 * n), a i > 0 := h2
    have h8 : ( (∑ i : Fin (2 * n), a i) / 2 ) / ( (∑ i : Fin (2 * n), a i) / 2 ) = (1 : ℝ) := by
      have h7 : (∑ i : Fin (2 * n), a i ) > 0 := h2
      field_simp
      <;> ring
    nlinarith [h8]