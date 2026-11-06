import Mathlib

open Finset
theorem algebra_163240 (a : ℕ → ℝ):
    ∃ r, (∀ n, a (n + 1) = r * a (n)) →
    {n | ∑ i in Finset.Icc 1 n, a i = 0}.Infinite := by 
  use (0 : ℝ)
  intro h
  have h1 : ∀ (n : ℕ), a (n + 1) = 0 := by
    intro n
    specialize h n
    simpa using h

  have h2 : ∀ (n : ℕ), ∑ i in Finset.Icc 1 n, a i = 0 := by
    intro n
    have h3 : ∀ i ∈ Finset.Icc 1 n, a i = 0 := by
      intro i hi
      have h4 : i ≥ 1 := by
        have h5 : i ∈ Finset.Icc 1 n := hi
        simp at h5 ⊢
        omega

      have h5 : i ≥ 1 := h4
      have h7 : ∃ k : ℕ, i = k + 1 := by
        refine' ⟨i - 1, by omega⟩

      rcases h7 with ⟨k, hk⟩
      have h8 : i = k + 1 := hk
      rw [show i = k + 1 by linarith]
      specialize h1 k
      simpa using h1

    have h7 : ∑ i in Finset.Icc 1 n, a i = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have h3' : a i = 0 := h3 i hi
      simpa using h3'

    exact_mod_cast h7

  have h3 : {n | ∑ i in Finset.Icc 1 n, a i = 0} = Set.univ := by
    ext n
    simp [h2 n]

  rw [h3]
  exact Set.infinite_univ