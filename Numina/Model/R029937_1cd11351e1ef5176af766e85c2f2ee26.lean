import Mathlib

open Finset Real

theorem algebra_253417 {n : ℕ} :
    ∑ i ∈ range n, (i + 1) / ((i + 2) * (i + 3) * (i + 4)) = n * (n + 1) / (4 * (n + 2) * (n + 3)) := by
  have h1 : ∀ i : ℕ, (i + 1) / ((i + 2) * (i + 3) * (i + 4)) = 0 := by
    intro i
    have h2 : (i + 1) < (i + 2) * (i + 3) * (i + 4) := by
      nlinarith [sq_nonneg (i : ℕ), sq_nonneg ((i + 1 : ℕ)), sq_nonneg ((i + 2 : ℕ)), sq_nonneg ((i + 3 : ℕ)), sq_nonneg ((i + 4 : ℕ)), 
        mul_nonneg (show (0 : ℕ) ≤ i by linarith) (show (0 : ℕ) ≤ i + 1 by linarith), 
        mul_nonneg (show (0 : ℕ) ≤ i by linarith) (show (0 : ℕ) ≤ i + 2 by linarith)]
    have h3 : (i + 1) / ((i + 2) * (i + 3) * (i + 4)) = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    exact h3

  have h4 : ∑ i in range n, (i + 1) / ((i + 2) * (i + 3) * (i + 4)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    specialize h1 i
    simpa using h1

  have h5 : n * (n + 1) / (4 * (n + 2) * (n + 3)) = 0 := by
    have h8 : n * (n + 1) < 4 * (n + 2) * (n + 3) := by
      nlinarith [sq_nonneg (n : ℕ), sq_nonneg ((n + 1 : ℕ)), sq_nonneg ((n + 2 : ℕ)), sq_nonneg ((n + 3 : ℕ)), 
        mul_nonneg (show (0 : ℕ) ≤ n by linarith) (show (0 : ℕ) ≤ n + 1 by linarith)]
    have h9 : n * (n + 1) / (4 * (n + 2) * (n + 3)) = 0 := by
      rw [Nat.div_eq_zero_iff]
      omega
    exact h9

  rw [h4, h5]