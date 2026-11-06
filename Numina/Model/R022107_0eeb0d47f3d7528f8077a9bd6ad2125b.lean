import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_157570 (f : ℝ → ℝ) (hf : f = λ x => x^2 + 25 + abs (x^3 - 5 * x^2)) :
    ∀ a, (∀ x ∈ Icc 1 12, f x ≥ a * x) ↔ a ≤ 10 := by
  intro a
  constructor
  · -- First, we verify that if $f(x)\geqslant ax$ holds for all $x$ in $[1, 12]$, then $a\leqslant 10$.
    intro h
    have h5 := h 5 (by norm_num)
    simp [hf] at h5
    norm_num [abs_of_nonneg, abs_of_nonpos] at h5
    nlinarith
  · -- Next, we verify that if $a \leqslant 10$, then $f(x)\geqslant ax$ holds for all $x$ in $[1, 12]$.
    intro ha x hx
    have h1 : 1 ≤ x ∧ x ≤ 12 := by
      simp at hx ⊢
      constructor <;> linarith
    have h2 : x ≥ 1 := h1.1
    have h3 : x ≤ 12 := h1.2
    have h4 : f x = x ^ 2 + 25 + abs (x ^ 3 - 5 * x ^ 2) := by
      simp [hf]
    by_cases h5 : x ^ 3 - 5 * x ^ 2 ≥ 0
    · -- when x^3 -5x^2 >=0, i.e., x >=5
      have h6 : abs (x ^ 3 - 5 * x ^ 2) = x ^ 3 - 5 * x ^ 2 := by
        rw [abs_of_nonneg h5]
      have h7 : f x = x ^ 3 - 4 * x ^ 2 + 25 := by
        rw [h4, h6]
        ring
      have h8 : f x ≥ 10 * x := by
        rw [h7]
        nlinarith [sq_nonneg (x - 5), sq_nonneg (x ^ 2 + x - 5), sq_nonneg (x ^ 2 - x + 5), sq_nonneg ((x) ^ 2 - 25)]
      nlinarith [h8, ha, mul_self_nonneg (x - 5)]
    · -- when x <5
      have h6 : abs (x ^ 3 - 5 * x ^ 2) = 5 * x ^ 2 - x ^ 3 := by
        rw [abs_of_neg (show x ^ 3 - 5 * x ^ 2 < 0 by nlinarith)]
        nlinarith
      have h7 : f x = 6 * x ^ 2 - x ^ 3 + 25 := by
        rw [h4, h6]
        ring
      have h8 : f x ≥ 10 * x := by
        rw [h7]
        nlinarith [sq_nonneg (x - 5), sq_nonneg (x ^ 2 - x + 5), sq_nonneg ((x - 1) * (x - 5)), sq_nonneg (x * (x - 5))]
      nlinarith [h8, ha, mul_self_nonneg (x - 5)]