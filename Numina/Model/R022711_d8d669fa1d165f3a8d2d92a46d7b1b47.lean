import Mathlib

open Nat

theorem inequalities_225979 (k : ℕ) :
    ∑ i ∈ Finset.Icc 1 k, i * factorial i < factorial (k + 1) := by
  have h1 : ∀ (k : ℕ), ∑ i ∈ Finset.Icc 1 k, i * factorial i < factorial (k + 1) := by
    intro k
    induction k with 
    | zero =>
      simp [Finset.sum_eq_zero] 
    | succ k ih =>
      rw [Finset.sum_Icc_succ_top (by norm_num)]
      simp [Nat.factorial] at ih ⊢ 
      all_goals 
        linarith [ih, mul_pos (show 0 < 1 by norm_num) (show 0 < 1 by norm_num)]
  specialize h1 k
  simpa using h1