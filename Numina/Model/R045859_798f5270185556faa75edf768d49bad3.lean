import Mathlib

open Finset Real

theorem algebra_318923 {n : ℕ} :
    ∑ i ∈ range n, (1 / ((i + 1) * (i + 2) * (i + 3))) =
    ((1 / 2) * (1 / (1 * 2) - 1 / ((n + 1) * (n + 2)))) := by 
  have h1 : ∀ n : ℕ, ∑ i ∈ range n, (1 / ((i + 1) * (i + 2) * (i + 3))) =
      ((1 / 2) * (1 / (1 * 2) - 1 / ((n + 1) * (n + 2)))) := by
    intro n 
    induction n with 
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      field_simp at *
      <;> ring_nf <;> omega 
  exact h1 n