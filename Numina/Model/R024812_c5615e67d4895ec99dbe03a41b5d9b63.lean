import Mathlib

open Real
open scoped BigOperators

theorem inequalities_599902 {n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
  (ha : ∀ i, 0 < a i) (h : ∏ i, a i = 1) :
  ∑ i, a i ≥ n := by

  have h1 : ∀ i : Fin n, a i - 1 ≥ Real.log (a i) := by
    intro i
    have h2 : 0 < a i := ha i
    have h3 : a i - 1 ≥ Real.log (a i) := by
      linarith [Real.log_le_sub_one_of_pos h2]
    exact h3

  have h4 : ∑ i : Fin n, (a i - 1) ≥ ∑ i : Fin n, Real.log (a i) := by
    apply Finset.sum_le_sum
    intro i hi
    specialize h1 i
    linarith

  have h5 : ∑ i : Fin n, (a i - 1) = ∑ i : Fin n, a i - n := by
    calc
      ∑ i : Fin n, (a i - 1) = ∑ i : Fin n, a i - ∑ i : Fin n, (1 : ℝ) := by
        rw [Finset.sum_sub_distrib]
      _ = ∑ i : Fin n, a i - n := by
        simp

  have h6 : ∑ i : Fin n, Real.log (a i) = Real.log (∏ i : Fin n, (a i)) := by
    rw [Real.log_prod]
    all_goals
      intro i hi
      have h7 : 0 < a i := ha i
      linarith

  have h7 : Real.log (∏ i : Fin n, (a i)) = (0 : ℝ) := by
    rw [h]
    simp

  have h8 : ∑ i : Fin n, Real.log (a i) = (0 : ℝ) := by
    rw [h6, h7]

  linarith [h4, h5, h8]