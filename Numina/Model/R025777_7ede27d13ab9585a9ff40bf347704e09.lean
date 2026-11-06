import Mathlib

open Topology Filter Real Complex TopologicalSpace Finset
open scoped BigOperators

theorem inequalities_188360 :
  IsGreatest {x | ∀ a : Fin 25 → ℝ, (∃ n : ℤ, ∑ i : Fin 25, a i = n) →
    ∃ i : Fin 25, |a i - 1 / 2| ≥ x} 0.02 := by
  constructor
  · -- Show 0.02 is in the set
    intro a h
    rcases h with ⟨n, hn⟩
    by_contra h'
    push_neg at h'
    have h1 : ∀ i : Fin 25, |a i - 1 / 2| < (0.02 : ℝ) := by
      intro i
      simpa using h' i
    have h2 : ∀ i : Fin 25, - (0.02 : ℝ) < a i - 1 / 2 := by
      intro i
      have h1' : |a i - 1 / 2| < (0.02 : ℝ) := h1 i
      cases' abs_lt.mp h1' with h3 h4
      linarith
    have h3 : ∀ i : Fin 25, a i - 1 / 2 < (0.02 : ℝ) := by
      intro i
      have h1' : |a i - 1 / 2| < (0.02 : ℝ) := h1 i
      cases' abs_lt.mp h1' with h3 h4
      linarith
    have h4 : ∀ i : Fin 25, (0.48 : ℝ) < a i := by
      intro i
      have h5 : a i - 1 / 2 > - (0.02 : ℝ) := by
        simpa using h2 i
      have h6 : a i > (0.48 : ℝ) := by
        norm_num at h5 ⊢
        linarith
      exact_mod_cast h6
    have h5 : ∀ i : Fin 25, a i < (0.52 : ℝ) := by
      intro i
      have h5 : a i - 1 / 2 < (0.02 : ℝ) := by
        simpa using h3 i
      have h6 : a i < (0.52 : ℝ) := by
        norm_num at h5 ⊢
        linarith
      exact_mod_cast h6
    have h6 : ∑ i : Fin 25, a i = (↑n : ℝ) := by
      simpa using hn
    have h7 : ∑ i : Fin 25, a i = ↑n := by
      linarith
    have h8 : (↑n : ℝ) > (12 : ℝ) := by
      have h9 : ∑ i : Fin 25, a i > (12 : ℝ) := by
        calc
          ∑ i : Fin 25, a i = ∑ i : Fin 25, (a i) := by
            rfl
          _ > ∑ i : Fin 25, (0.48 : ℝ) := by
            apply Finset.sum_lt_sum
            · -- Show that each element is greater or equal
              intro i _
              specialize h4 i
              norm_num at h4 ⊢
              linarith
            · -- Show that there is an element that is greater
              use ⟨0, by simp⟩
              simp at *
              --show that 0.48 < a 0
              specialize h4 ⟨0, by simp⟩
              norm_num at h4 ⊢
              linarith
          _ = (12 : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]
            <;> norm_num
      linarith
    have h9 : (↑n : ℝ) < (13 : ℝ) := by
      have h9 : ∑ i : Fin 25, a i < (13 : ℝ) := by
        calc
          ∑ i : Fin 25, a i = ∑ i : Fin 25, (a i) := by
            rfl
          _ < ∑ i : Fin 25, (0.52 : ℝ) := by
            apply Finset.sum_lt_sum
            · -- Show that each element is less or equal
              intro i _
              specialize h5 i
              norm_num at h5 ⊢
              linarith
            · -- Show that there is an element that is less
              use ⟨0, by simp⟩
              simp at *
              --show 0.48 < a 0
              specialize h5 ⟨0, by simp⟩
              norm_num at h5 ⊢
              linarith
          _ = (13 : ℝ) := by
            simp [Finset.sum_const, Finset.card_univ]
            <;> norm_num
      linarith
    have hn1 : n > 12 := by
      by_contra h
      push_neg at h
      have hn2 : n ≤ 12 := by
        omega
      have h10 : (↑n : ℝ) ≤ (12 : ℝ) := by
        exact_mod_cast hn2
      nlinarith
    have hn2 : n < 13 := by
      by_contra h
      push_neg at h
      have hn3 : n ≥ 13 := by
        omega
      have h10 : (↑n : ℝ) ≥ (13 : ℝ) := by
        exact_mod_cast hn3
      nlinarith
    have hn3 : n = 12 := by
      omega
    have hn4 : (↑n : ℝ) = (12 : ℝ) := by
      exact_mod_cast hn3
    nlinarith
  · -- Show that 0.02 is the greatest
    intro x hx
    have h : ∀ a : Fin 25 → ℝ, (∃ n : ℤ, ∑ i : Fin 25, a i = n) →
        ∃ i : Fin 25, |a i - 1 / 2| ≥ x := hx
    have h1 := h (fun i : Fin 25 => (0.48 : ℝ)) (by
      use 12
      simp [Finset.sum_const, Finset.card_univ]
      <;> norm_num
    )
    rcases h1 with ⟨i, hi⟩
    have h2 : |(0.48 : ℝ) - (1 / 2 : ℝ)| ≥ x := by
      simpa using hi
    have h3 : |(0.48 : ℝ) - (1 / 2 : ℝ)| = (0.02 : ℝ) := by
      norm_num [abs_of_nonneg, abs_of_nonpos]
    have h4 : (0.02 : ℝ) ≥ x := by
      linarith [h2, h3]
    linarith