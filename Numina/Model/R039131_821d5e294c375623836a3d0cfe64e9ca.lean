import Mathlib

open Finset Real

theorem algebra_245415 {n : ℕ} (hn : 2 ≤ n) :
    ∑ k ∈ Icc 1 n, (k / (1 + k ^ 2 + k ^ 4)) *
    ∏ k ∈ Icc 2 n, ((k ^ 3 - 1) / (k ^ 3 + 1)) = 1 / 3 := by
  have h1 : ∀ n : ℕ, n ≥ 2 → ∑ k ∈ Icc 1 n, (k / (1 + k ^ 2 + k ^ 4)) *
    ∏ k ∈ Icc 2 n, ((k ^ 3 - 1) / (k ^ 3 + 1)) = 1 / 3 := by 
    intro n hn
    induction n with
    | zero =>
      exfalso
      linarith
    | succ n ih =>
      rcases n with _ | n
      · -- n = 0, so original n = 1, contradiction with hn: 2 <= n
        exfalso
        linarith
      · -- n = k + 1, where k is the current n
        simp [Finset.sum_Icc_succ_top, Finset.prod_Icc_succ_top, mul_add, mul_assoc] at *
        all_goals
          norm_num [Finset.sum_Icc_succ_top, Finset.prod_Icc_succ_top] at *
          <;> try { linarith }
          <;> try { tauto }
  specialize h1 n hn
  simpa using h1