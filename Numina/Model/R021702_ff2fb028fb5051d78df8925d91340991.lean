import Mathlib

open Finset Real

theorem algebra_110519 {n : ℕ} (hn : 0 < n) (S : ℕ → ℝ)
    (hS : ∀ k, S k = ∑ i ∈ Icc 1 k, (1 : ℝ)/i) :
    ∑ i ∈ Icc 1 n, i * S i = (n * (n + 1))/2 * (S (n + 1) - 1/2) := by

  have h1 : ∀ n : ℕ, ∑ i ∈ Icc 1 n, i * S i = (n * (n + 1))/2 * (S (n + 1) - 1/2) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      cases n with
      | zero =>
        simp [hS] at ih ⊢
        <;> norm_num [Finset.sum_Icc_succ_top, mul_add] at ih ⊢
        <;> linarith
      | succ n =>
        rw [sum_Icc_succ_top (by linarith)]
        rw [ih]
        simp [hS, sum_Icc_succ_top] at *
        field_simp at *
        ring
  specialize h1 n
  simpa using h1