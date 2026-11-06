import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_598956 {n : ℕ} (hn : 0 < n) (x : Fin n → ℝ)
  (h₁ : ∀ i, |x i| < 1) (h₂ : ∑ i, |x i| = 19 + |∑ i, x i|) :
  n ≥ 20 := by
  by_contra h
  push_neg at h
  have h3 : n ≤ 19 := by linarith
  have h4 : ∑ i : Fin n, |x i| < (n : ℝ) := by
    have h5 : ∀ i : Fin n, |x i| < 1 := by
      intro i
      apply h₁ i
    have h6 : ∑ i : Fin n, |x i| < ∑ i : Fin n, (1 : ℝ) := by
      apply Finset.sum_lt_sum
      · intro i hi
        specialize h5 i
        linarith
      · use ⟨0, by linarith [hn]⟩
        simp [h5]
    have h7 : ∑ i : Fin n, (1 : ℝ) = (n : ℝ) := by simp [Finset.sum_const, Finset.card_univ]
    linarith [h6, h7]
  have h8 : |∑ i : Fin n, x i| ≥ 0 := abs_nonneg (∑ i, x i)
  have h9 : ∑ i : Fin n, |x i| ≥ (19 : ℝ) := by
    linarith [h₂, abs_nonneg (∑ i, x i)]
  have h10 : (n : ℝ) > (19 : ℝ) := by
    linarith [h9, h4]
  have h11 : n > 19 := by
    have h12 : (n : ℝ) ≤ (19 : ℝ) := by
      have h : n ≤ 19 := by linarith
      exact_mod_cast h
    linarith
  omega