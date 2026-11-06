import Mathlib

open Finset Real

theorem algebra_191539 : ∏ i ∈ Icc 2 2006, (((i : ℕ)^2 : ℝ) / (i^2 - 1)) = (4012 : ℝ) / 2007 := by

  have h2 : ∀ (k : ℕ), k ≥ 2 → (∏ i ∈ Icc 2 k, (((i : ℕ)^2 : ℝ) / (i^2 - 1)) = (2 * k : ℝ) / (k + 1 : ℝ)) := by
    intro k hk
    have h4 : k ≥ 2 := hk
    have h3 : ∏ i ∈ Icc 2 k, (((i : ℕ)^2 : ℝ) / (i^2 - 1)) = (2 * k : ℝ) / (k + 1 : ℝ) := by
      have h5 : ∀ (n : ℕ), ∏ i ∈ Icc 2 (n + 2), (((i : ℕ)^2 : ℝ) / (i^2 - 1)) = (2 * ((n + 2) : ℝ) ) / (( (n + 2) + 1 : ℝ ) ) := by
        intro n
        induction n with
        | zero =>
          norm_num
        | succ n ih =>
          rw [show n + 2 + 1 = n + 3 by omega]
          rw [prod_Icc_succ_top (by linarith)]
          rw [ih]
          field_simp at *
          ring_nf at *
          <;> field_simp at *
          all_goals ring_nf 
      have h6 : k ≥ 2 := h4
      have h7 : ∃ m, k = m + 2 := by
        use k - 2
        omega
      rcases h7 with ⟨m, hm⟩
      rw [show k = m + 2 by linarith [hm]] 
      specialize h5 m
      simpa using h5
    exact h3

  have h3 := h2 2006 (by norm_num)
  rw [h3]
  norm_num