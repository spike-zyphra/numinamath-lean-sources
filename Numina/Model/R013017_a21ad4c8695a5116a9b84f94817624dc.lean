import Mathlib
open Finset Real

theorem inequalities_1059 {n : ℕ} (hn : 0 < n) (a b : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) :
  n ≤ ∑ i, a i / b i ∨ n ≤ ∑ i, b i / a i := by
  by_contra h
  push_neg at h 
  have h1 : ∑ i : Fin n, a i / b i < n := by
    simpa using h.1
  have h2 : ∑ i : Fin n, b i / a i < n := by
    simpa using h.2
  have h3 : ∀ i : Fin n, 0 < a i := by
    intro i
    apply ha
  have h4 : ∀ i : Fin n, 0 < b i := by
    intro i
    apply hb
  have h5 : ∑ i : Fin n, (a i / b i + b i / a i) ≥ 2 * n := by
    have h6 : ∀ i : Fin n, a i / b i + b i / a i ≥ 2 := by
      intro i
      have ha_pos : 0 < a i := h3 i
      have hb_pos : 0 < b i := h4 i
      have h7 : a i / b i + b i / a i - 2 ≥ 0 := by
        have h8 : a i / b i + b i / a i - 2 = (a i ^ 2 + b i ^ 2 - 2 * a i * b i) / ( (a i) * (b i) ) := by
          field_simp
          <;> ring
        rw [h8]
        have h9 : (a i ^ 2 + b i ^ 2 - 2 * a i * b i) = (a i - b i) ^ 2 := by
          ring
        rw [h9]
        have h10 : (a i - b i) ^ 2 ≥ 0 := by
          exact pow_two_nonneg (a i - b i)
        have h11 : (a i * b i) > 0 := by 
          positivity
        apply div_nonneg 
        · linarith
        · positivity
      linarith
    have h8 : ∑ i : Fin n, (a i / b i + b i / a i) ≥ ∑ i : Fin n, (2 : ℝ) := by 
      apply Finset.sum_le_sum 
      intro i hi
      specialize h6 i
      linarith 
    have h9 : ∑ i : Fin n, (2 : ℝ) = (n : ℝ) * (2 : ℝ) := by 
      simp 
    have h10 : (n : ℝ) * (2 : ℝ) = (2 * n : ℝ) := by 
      ring 
    linarith [h8, h9, h10]
  have h13 : (∑ i : Fin n, a i / b i) + (∑ i : Fin n, b i / a i) < 2 * (n : ℝ) := by 
    have h14 : ∑ i : Fin n, a i / b i < (n : ℝ) := by 
      simpa using h1 
    have h15 : ∑ i : Fin n, b i / a i < (n : ℝ) := by 
      simpa using h2 
    linarith [h14, h15]
  have h14 : (∑ i : Fin n, a i / b i) + (∑ i : Fin n, b i / a i) ≥ 2 * (n : ℝ) := by
    have h15 : ∑ i : Fin n, (a i / b i + b i / a i) = (∑ i : Fin n, (a i / b i)) + (∑ i : Fin n, (b i / a i)) := by 
      simp [Finset.sum_add_distrib]
    linarith [h15, h5]
  linarith [h13, h14]