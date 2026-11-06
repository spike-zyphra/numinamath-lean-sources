import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_226279 (n : ℕ) (x : Fin n → ℝ)
  (hx : ∀ i, x i ∈ Icc 0 1) :
  (∑ i, x i + 1) ^ 2 ≥ 4 * ∑ i, (x i) ^ 2 := by
  have hn01 : ∀ i : Fin n, 0 ≤ x i ∧ x i ≤ 1 := by
    intro i
    have h44 := hx i
    simpa using h44
  have h5 : ∑ i : Fin n, (x i) ^ 2 ≤ (∑ i : Fin n, x i) := by
    have h6 : ∀ i : Fin n, (x i) ^ 2 ≤ x i := by
      intro i 
      have h2 : 0 ≤ x i := by
        have h66 := hn01 i 
        exact h66.left
      have h3 : x i ≤ 1 := by
        have h67 := hn01 i
        exact h67.right
      nlinarith [sq_nonneg (x i - 1 / 2) ]
    have h7 : ∑ i : Fin n, (x i) ^ 2 ≤ ∑ i : Fin n, x i := by
      apply Finset.sum_le_sum 
      intro i hi
      specialize h6 i 
      linarith
    exact h7
  have h6 : (∑ i : Fin n, x i + 1 ) ^ 2 ≥ 4 * (∑ i : Fin n, (x i) ^ 2) := by
    nlinarith [sq_nonneg ((∑ i : Fin n, x i ) - 1 ), 
      h5, 
      show (∑ i : Fin n, x i ) ≥ 0 by
        have h8 : ∀ i : Fin n, 0 ≤ x i := by 
          intro i
          have h011 := hn01 i
          exact h011.left 
        have h9 : ∑ i : Fin n, x i ≥ 0 := by 
          apply Finset.sum_nonneg 
          intro i hi 
          exact h8 i  
        linarith 
    ]
  linarith