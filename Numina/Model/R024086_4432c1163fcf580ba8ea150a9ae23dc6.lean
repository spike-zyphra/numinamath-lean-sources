import Mathlib

open Finset Real

theorem algebra_137007 {n : ℕ} (hn : n > 0) (a b c : ℝ) :
    (∑ i ∈ range n, (a + b + c) / n) = (∑ i ∈ range n, a / n) +
    (∑ i ∈ range n, b / n) + (∑ i ∈ range n, c / n) := by 
  have h1 : (∑ i in range n, (a + b + c) / n) = n * ((a + b + c) / n) := by 
    simp [Finset.sum_const, Finset.card_range]
    <;> ring
  have h2 : (∑ i in range n, a / n) = n * (a / n) := by 
    simp [Finset.sum_const, Finset.card_range]
    <;> ring
  have h3 : (∑ i in range n, b / n) = n * (b / n) := by 
    simp [Finset.sum_const, Finset.card_range]
    <;> ring
  have h4 : (∑ i in range n, c / n) = n * (c / n) := by 
    simp [Finset.sum_const, Finset.card_range]
    <;> ring
  rw [h1, h2, h3, h4]
  field_simp at *
  <;> ring_nf <;> norm_num