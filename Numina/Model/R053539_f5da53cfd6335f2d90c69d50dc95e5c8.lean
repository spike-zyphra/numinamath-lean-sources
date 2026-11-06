import Mathlib

open Finset Real

theorem algebra_200791 (x : ℕ → ℝ) (hx1 : x 1 = 1 / 2)
    (hxn : ∀ n ≥ 2, x n = x (n - 1) / (2 * n * x (n - 1) + 1)) :
    ∑ i ∈ range 2018, x (i + 1) = 2018 / 2019 := by

  have eqn (n : ℕ) : x (n + 1) = 1 / ((n + 1 : ℕ) * ((n + 1 : ℕ) + (1 : ℝ))) := by
    induction n with
    | zero =>
      rw [show (0 + 1 : ℕ) = 1 by omega]
      norm_num [hx1]
    | succ n ih =>
      have h1 : (n + 1 + 1 : ℕ) = (n + 1) + 1 := by simp
      rw [show (n + 1 + 1 : ℕ) = (n + 1) + 1 by simp]
      specialize hxn (n + 2) (by omega)
      simp [show (n + 2 - 1 : ℕ) = n + 1 by omega] at hxn
      rw [hxn, ih]
      field_simp
      ring_nf
      <;> field_simp <;> ring

  have h2018 : ∀ n : ℕ, ∑ i ∈ range n, x (i + 1) = 1 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      have h1 : x (n + 1) = 1 / ((n + 1 : ℝ) * ((n + 1 : ℝ) + 1)) := by
        specialize eqn n
        simpa using eqn
      rw [h1]
      field_simp
      ring_nf
      <;> field_simp <;> ring

  specialize h2018 2018
  norm_num at h2018 ⊢
  <;> linarith