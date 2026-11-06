import Mathlib

open Finset Real

theorem algebra_286045 {n : ℕ} :
    ∑ i ∈ Icc 1 n, (1 / ((i * (i + 1)) : ℝ)) = n / (n + 1 : ℝ) := by 
  have h1 : ∀ (n : ℕ), ∑ i ∈ Icc 1 n, (1 / ((i * (i + 1)) : ℝ)) = n / (n + 1 : ℝ) := by 
    intro n 
    induction n with 
    | zero => 
      norm_num [sum_eq_zero]
    | succ n ih =>
      rw [sum_Icc_succ_top (by linarith)]
      rw [ih]
      field_simp at *
      <;> ring_nf
      <;> field_simp
      <;> ring
  specialize h1 n
  simpa using h1