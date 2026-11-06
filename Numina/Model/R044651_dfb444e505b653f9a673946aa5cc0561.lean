import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_280481 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (hx : ∀ i, -1 ≤ x i ∧ x i ≤ 1)
  (h : ∑ i, (x i)^3 = 0) :
  ∑ i, x i ≤ n / 3 := by
  have h1 : ∀ i, -1 ≤ x i ∧ x i ≤ 1 := hx
  have h2 : ∀ i, (x i) ^ 3 ≥ (3 / 4) * (x i) - 1 / 4 := by
    intro i
    rcases h1 i with ⟨h1_i, h2_i⟩
    nlinarith [sq_nonneg ((x i) - 1), sq_nonneg ((x i) ), sq_nonneg ((x i) + 1), sq_nonneg ((x i)^2 - 1/4), sq_nonneg ((x i) - 1/2), sq_nonneg ((x i) + 1/2), 
          mul_nonneg (show (0 : ℝ) ≤ (x i + 1) by linarith) (show (0 : ℝ) ≤ (1 - (x i)) by linarith)
          ]
  have h3 : ∑ i, (x i)^3 ≥ ∑ i, ((3 / 4) * (x i) - 1 / 4) := by
    apply Finset.sum_le_sum
    intro i _
    have h4 : (x i)^3 ≥ (3 / 4) * (x i) - 1 / 4 := h2 i
    linarith
  have h4 : ∑ i, ((3 / 4) * (x i) - 1 / 4) = (3 / 4) * (∑ i, (x i)) - (n / 4 : ℝ) := by
    simp [Finset.mul_sum, Finset.sum_mul, Finset.sum_const, Finset.card_univ, mul_comm]
    <;> ring
  have h5 : (3 / 4) * (∑ i, (x i)) - (n / 4 : ℝ) ≤ 0 := by
    nlinarith [h, h3, h4]
  have h6 : ∑ i, x i ≤ (n / 3 : ℝ) := by
    nlinarith [h5]
  linarith [h6]
  <;> nlinarith
  <;> nlinarith
  <;> nlinarith
  <;> nlinarith
  <;> nlinarith
  <;> nlinarith