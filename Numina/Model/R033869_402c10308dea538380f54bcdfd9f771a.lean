import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem algebra_299751 {a : ℕ → ℝ} {q : ℝ} (hq : 0 < |q| ∧ |q| < 1)
  (h : ∀ n, a n = a 0 * q ^ n) :
  ∃ S, ∀ n, ∑ i in range n, a i = S * (1 - q ^ n) := by

  have h1 : q ≠ 1 := by
    by_contra h1
    have h2 : |q| = 1 := by
      rw [h1]
      norm_num
    linarith [hq.2]

  have h2 : q ≠ -1 := by
    by_contra h2
    have h3 : |q| = 1 := by
      rw [h2]
      norm_num [abs_of_nonneg, abs_of_nonpos]
    linarith [hq.2]

  have h3 : q ≠ 0 := by
    by_contra h3
    have h4 : |q| = 0 := by
      rw [h3]
      norm_num
    linarith [hq.1]

  use (a 0 / (1 - q))

  intro n

  have h4 : ∀ (n : ℕ), ∑ i in range n, a i = a 0 / (1 - q) * (1 - q ^ n) := by
    intro n
    induction n with
    | zero =>
      simp
    | succ n ih =>
      rw [sum_range_succ, ih]
      have eq1 : a n = a 0 * q ^ n := by
        apply h
      rw [eq1]
      field_simp [(show (1 - q : ℝ) ≠ 0 by
        by_contra h4
        have hq1 : q = 1 := by
          linarith
        contradiction
      )]
      <;> ring

  specialize h4 n
  linarith [h4]