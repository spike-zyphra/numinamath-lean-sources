import Mathlib

open Real

lemma lemma_1 (n : ℕ) (y : Fin n → ℝ) (hsum : ∑ i : Fin n, y i > 0) :
    ∑ i : Fin n, (y i)^2 + ∑ i : Fin n, y i > 0 := by
  by_contra h
  push_neg at h
  have h2 : ∀ i : Fin n, (y i) ^ 2 ≥ 0 := by
    intro i
    exact sq_nonneg (y i)
  have h3 : ∑ i : Fin n, (y i) ^ 2 ≥ 0 := by
    apply Finset.sum_nonneg
    intro i hi
    exact h2 i
  have h4 : ∑ i : Fin n, (y i) ^ 2 + ∑ i : Fin n, y i > 0 := by
    have h10 : ∑ i : Fin n, (y i) ^ 2 ≥ 0 := h3
    linarith [h10, hsum]
  linarith [h, h4]


theorem inequalities_251324 (n : ℕ) (x : Fin n → ℝ) (h : ∑ i : Fin n, x i > n) :
    ∑ i : Fin n, (x i)^2 > ∑ i : Fin n, x i := by
  by_contra h'
  push_neg at h'
  have h4 : (∑ i : Fin n, x i) > (↑n : ℝ) := by
    simpa using h
  have h7 : (∑ i : Fin n, (x i) ^ 2) ≤ (∑ i : Fin n, x i) := by
    linarith [h']
  have h8 : (∑ i : Fin n, (1 : ℝ) * (x i)) ^ 2 ≤ (∑ i : Fin n, (1 : ℝ) ^ 2) * (∑ i : Fin n, (x i) ^ 2) := by
    apply Finset.sum_mul_sq_le_sq_mul_sq
  have h9 : (∑ i : Fin n, (1 : ℝ) * (x i)) = (∑ i : Fin n, x i) := by
    simp_all [Finset.sum_mul, mul_comm]
    all_goals try { tauto }
  have h10 : (∑ i : Fin n, (1 : ℝ) ^ 2) = (↑n : ℝ) := by
    simp_all [Finset.sum_const, Finset.card_univ]
  have h2 : (∑ i : Fin n, (1 : ℝ) * (x i)) ^ 2 ≤ (∑ i : Fin n, (1 : ℝ) ^ 2) * (∑ i : Fin n, (x i) ^ 2) := h8
  have h3 : (∑ i : Fin n, x i) ^ 2 ≤ (↑n : ℝ) * (∑ i : Fin n, (x i) ^ 2) := by
    rw [show (∑ i : Fin n, (1 : ℝ) * (x i)) = (∑ i : Fin n, x i) by nlinarith [h9]] at h2
    rw [show (∑ i : Fin n, (1 : ℝ) ^ 2) = (↑n : ℝ) by nlinarith [h10]] at h2
    nlinarith
  have h11 : (∑ i : Fin n, x i) ^ 2 ≤ (↑n : ℝ) * (∑ i : Fin n, x i) := by
    nlinarith [h3, h7]
  -- Now reach contradiction
  have h6 : (∑ i : Fin n, x i) * ((∑ i : Fin n, x i) - (↑n : ℝ)) ≤ 0 := by
    nlinarith
  -- Now reach contradiction
  nlinarith [h4, sq_nonneg ((∑ i : Fin n, x i) - (↑n : ℝ)), sq_nonneg ((∑ i : Fin n, x i)), sq_pos_of_pos (show 0 < (∑ i : Fin n, x i - ↑n) by nlinarith), sq_pos_of_pos (show 0 < (∑ i : Fin n, x i) by nlinarith)]