import Mathlib

open Finset Real

theorem inequalities_598110 {n : ℕ} (hn : 0 < n) (a b c d : Fin n → ℝ)
    (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i) (hc : ∀ i, 0 < c i) (hd : ∀ i, 0 < d i) :
    (∑ i, a i * b i * c i * d i) ^ 4 ≤
    (∑ i, a i ^ 4) * (∑ i, b i ^ 4) * (∑ i, c i ^ 4) * (∑ i, d i ^ 4) := by
  have h1 : (∑ i, a i * b i * c i * d i) ^ 4 ≤ (∑ i, a i ^ 4) * (∑ i, b i ^ 4) * (∑ i, c i ^ 4) * (∑ i, d i ^ 4) := by
    have h11 : (∑ i, a i * b i * c i * d i) ^ 2 ≤ (∑ i, (a i * d i) ^ 2) * (∑ i, (b i * c i) ^ 2) := by
      have h1 : (∑ i, a i * b i * c i * d i) ^ 2 = (∑ i, (a i * d i) * (b i * c i)) ^ 2 := by
        congr
        funext i
        ring
      rw [h1]
      have h2 : (∑ i, (a i * d i) * (b i * c i)) ^ 2 ≤ (∑ i, (a i * d i) ^ 2) * (∑ i, (b i * c i) ^ 2) := by
        apply Finset.sum_mul_sq_le_sq_mul_sq
      linarith
    have h12 : (∑ i, (a i * d i) ^ 2) ^ 2 ≤ (∑ i, a i ^ 4) * (∑ i, d i ^ 4) := by
      have h2 : (∑ i, (a i * d i) ^ 2) ^ 2 ≤ (∑ i, a i ^ 4) * (∑ i, d i ^ 4) := by
        have h31 : (∑ i, (a i * d i) ^ 2) ^ 2 = (∑ i, (a i ^ 2) * (d i ^ 2)) ^ 2 := by
          congr
          funext i
          ring_nf
        rw [h31] at *
        have h7 : (∑ i, (a i ^ 2) * (d i ^ 2)) ^ 2 ≤ (∑ i, (a i ^ 2) ^ 2) * (∑ i, (d i ^ 2) ^ 2) := by
          apply Finset.sum_mul_sq_le_sq_mul_sq
        have h8 : (∑ i, (a i ^ 2) ^ 2) = (∑ i, a i ^ 4) := by
          congr
          funext i
          ring_nf
        have h9 : (∑ i, (d i ^ 2) ^ 2) = (∑ i, d i ^ 4) := by
          congr
          funext i
          ring_nf
        rw [h8, h9] at h7
        linarith
      linarith
    have h13 : (∑ i, (b i * c i) ^ 2) ^ 2 ≤ (∑ i, b i ^ 4) * (∑ i, c i ^ 4) := by
      have h3 : (∑ i, (b i * c i) ^ 2) ^ 2 ≤ (∑ i, b i ^ 4) * (∑ i, c i ^ 4) := by
        have h31 : (∑ i, (b i * c i) ^ 2) ^ 2 = (∑ i, (b i ^ 2) * (c i ^ 2)) ^ 2 := by
          congr
          funext i
          ring_nf
        rw [h31] at *
        have h7 : (∑ i, (b i ^ 2) * (c i ^ 2)) ^ 2 ≤ (∑ i, (b i ^ 2) ^ 2) * (∑ i, (c i ^ 2) ^ 2) := by
          apply Finset.sum_mul_sq_le_sq_mul_sq
        have h8 : (∑ i, (b i ^ 2) ^ 2) = (∑ i, b i ^ 4) := by
          congr
          funext i
          ring_nf
        have h9 : (∑ i, (c i ^ 2) ^ 2) = (∑ i, c i ^ 4) := by
          congr
          funext i
          ring_nf
        rw [h8, h9] at h7
        linarith
      linarith
    have h2 : (∑ i, a i * b i * c i * d i) ^ 4 = ((∑ i, a i * b i * c i * d i) ^ 2) ^ 2 := by
      ring_nf
    rw [h2]
    have h3 : ((∑ i, a i * b i * c i * d i) ^ 2) ^ 2 ≤ ((∑ i, (a i * d i) ^ 2) * (∑ i, (b i * c i) ^ 2)) ^ 2 := by
      have h4 : (∑ i, a i * b i * c i * d i) ^ 2 ≤ (∑ i, (a i * d i) ^ 2) * (∑ i, (b i * c i) ^ 2) := h11
      nlinarith [sq_nonneg ((∑ i, a i * b i * c i * d i) ^ 2 - (∑ i, (a i * d i) ^ 2) * (∑ i, (b i * c i) ^ 2))]
    have h4 : ((∑ i, (a i * d i) ^ 2) * (∑ i, (b i * c i) ^ 2)) ^ 2 ≤ ((∑ i, a i ^ 4) * (∑ i, d i ^ 4)) * ((∑ i, b i ^ 4) * (∑ i, c i ^ 4)) := by
      have h5 : (∑ i, (a i * d i) ^ 2) ^ 2 ≤ (∑ i, a i ^ 4) * (∑ i, d i ^ 4) := h12
      have h6 : (∑ i, (b i * c i) ^ 2) ^ 2 ≤ (∑ i, b i ^ 4) * (∑ i, c i ^ 4) := h13
      nlinarith [mul_nonneg (show (∑ i, a i ^ 4) ≥ 0 by positivity) (show (∑ i, d i ^ 4) ≥ 0 by positivity), 
        mul_nonneg (show (∑ i, b i ^ 4) ≥ 0 by positivity) (show (∑ i, c i ^ 4) ≥ 0 by positivity), 
        sq_nonneg ((∑ i, (a i * d i) ^ 2)^2 - (∑ i, a i ^ 4) * (∑ i, d i ^ 4)), 
        sq_nonneg ((∑ i, (b i * c i) ^ 2)^2 - (∑ i, b i ^ 4) * (∑ i, c i ^ 4))]
    linarith
  exact h1