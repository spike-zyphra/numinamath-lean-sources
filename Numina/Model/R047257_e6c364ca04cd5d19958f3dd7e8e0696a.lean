import Mathlib

open Finset Real

theorem algebra_600896 {n : ℕ} (hn : 0 < n) (a : ℕ → ℝ)
    (ha : ∀ i ∈ Icc 1 n, 0 < a i) (A : ℕ → ℝ)
    (hA : ∀ i ∈ Icc 1 n, A i = (∑ j in Icc 1 i, a j) / i) :
    ∀ i ∈ Icc 1 n, A i > 0 := by
  intro i hi
  have h1 : A i = (∑ j in Icc 1 i, a j) / i := by
    apply hA
    exact hi
  have h2 : i ≥ 1 := by
    have h3 : i ∈ Icc 1 n := hi
    simp at h3 ⊢
    omega
  have h3 : i ≤ n := by
    have h4 : i ∈ Icc 1 n := hi
    simp at h4 ⊢
    omega
  have h4 : (∑ j in Icc 1 i, a j) > 0 := by
    have h8 : ∀ j, j ∈ Icc 1 i → 0 < a j := by
      intro j h9
      have h10 : j ∈ Icc 1 n := by
        have h9' : j ∈ Icc 1 i := h9
        simp at h9' ⊢
        have h11 : 1 ≤ j := h9'.1
        have h12 : j ≤ i := h9'.2
        have h13 : i ≤ n := h3
        have h14 : j ≤ n := by linarith
        exact ⟨h11, h14⟩
      have h18 : 0 < a j := ha j h10
      exact h18
    have h9 : (∑ j in Icc 1 i, a j) > 0 := by
      apply Finset.sum_pos
      · exact h8
      · use 1
        have h14 : i ≥ 1 := h2
        simp at *
        all_goals
          omega
    exact h9
  have h7 : (i : ℝ) > 0 := by
    have h8 : i ≥ 1 := h2
    have h9 : (i : ℝ) ≥ (1 : ℝ) := by exact_mod_cast h8
    nlinarith
  rw [h1]
  apply div_pos
  · linarith
  · linarith