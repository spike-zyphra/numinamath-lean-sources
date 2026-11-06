import Mathlib

open Finset Real

theorem algebra_4422 {n : ℕ} (hn : 1 ≤ n) :
    ∑ i ∈ Icc 1 n, (1 / ((i * (i+1)) : ℝ)) = (n / (n+1 : ℝ)) := by
  have h1 : ∀ n : ℕ, 1 ≤ n → (∑ i ∈ Icc 1 n, (1 / ((i * (i+1)) : ℝ)) = (n / (n+1 : ℝ))) := by
    intro n hn
    induction n with
    | zero => 
      exfalso
      linarith
    | succ n ih =>
      cases n with
      | zero => 
        norm_num at ih ⊢
      | succ n => 
        rw [sum_Icc_succ_top (by linarith)]
        rw [ih (by linarith)]
        field_simp at *
        ring
  specialize h1 n hn
  simpa using h1