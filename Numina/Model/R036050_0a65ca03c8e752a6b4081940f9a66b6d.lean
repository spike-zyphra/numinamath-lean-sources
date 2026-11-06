import Mathlib

open Finset Real

theorem algebra_297248 (a : ℕ → ℚ) (ha1 : a 1 = 1)
    (han : ∀ n ≥ 1, a (n + 1) = a n + 2 * n) :
    ∑ k in Finset.Icc 1 2007, (1 / (a (k + 1) - 1)) = 2007 / 2008 := by

  have h1 : ∀ n : ℕ, a (n + 1) = (↑n + 1 : ℚ) ^ 2 - (↑n + 1 : ℚ) + 1 := by
    intro n
    induction n with
    | zero =>
      norm_num [ha1]
    | succ n ih =>
      have eq1 := han (n + 1) (by linarith)
      rw [show n + 1 + 1 = n + 2 by omega] at eq1
      rw [eq1]
      rw [ih]
      field_simp at *
      ring

  have h2 : ∀ k : ℕ, a (k + 1) - 1 = (↑k : ℚ) * ((↑k + 1 : ℚ)) := by
    intro k
    rw [h1 k]
    field_simp
    ring

  have h3 : ∀ (n : ℕ), ∑ k in Finset.Icc 1 n, (1 / (a (k + 1) - 1)) = 1 - 1 / ((↑n + 1 : ℚ)) := by
    intro n
    induction n with
    | zero =>
      norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by linarith)]
      rw [ih]
      rw [h2 (n + 1)]
      field_simp at *
      ring

  rw [h3 2007]
  norm_num