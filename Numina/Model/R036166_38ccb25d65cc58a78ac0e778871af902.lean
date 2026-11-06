import Mathlib

open Real
open scoped BigOperators

theorem inequalities_286160 (n : ℕ) (hn : 0 < n) :
  ∑ i ∈ Finset.Icc 1 n, (1 / (i ^ 2)) < 2 := by 
  have h1 : ∀ i : ℕ, i ≥ 2 → 1 / (i ^ 2) = 0 := by
    intro i hi
    have h2 : i ^ 2 ≥ 4 := by nlinarith
    have : 1 / (i ^ 2) = 0 := by
      norm_num
      all_goals omega
    assumption

  have h3 : ∀ n : ℕ, n ≥ 1 → ∑ i ∈ Finset.Icc 1 n, (1 / (i ^ 2)) = 1 := by
    intro n hn
    induction n with 
    | zero => linarith
    | succ n ih =>
      cases n with
      | zero => 
        simp [Finset.sum_Icc_succ_top]
        all_goals try { tauto }
      | succ n =>
        rw [Finset.sum_Icc_succ_top (by linarith)]
        rw [ih (by linarith)]
        have h5 : 1 / ((n + 1 + 1) ^ 2) = 0 := by 
          apply h1 
          all_goals omega 
        simp [h5]
        all_goals try { linarith }
  have h3' : ∑ i ∈ Finset.Icc 1 n, (1 / (i ^ 2)) = 1 := h3 n (by linarith)
  rw [h3']
  all_goals norm_num
  all_goals try { linarith }
  all_goals try { tauto }