import Mathlib

open Real
open scoped BigOperators

theorem inequalities_237776 (n : ℕ) (hn : 3 ≤ n) :
  ∑ i ∈ Finset.Icc 3 n, (i : ℝ) / ((i - 2).factorial + (i - 1).factorial + i.factorial) < 1 / 2 := by
  have h3 : ∑ i ∈ Finset.Icc 3 n, (i : ℝ) / ((i - 2).factorial + (i - 1).factorial + i.factorial) < (1 / 2 : ℝ) := by
    have h5 : ∑ i ∈ Finset.Icc 3 n, (i : ℝ) / ((i - 2).factorial + (i - 1).factorial + i.factorial) = (1 / 2 : ℝ) - (1 / (n.factorial : ℝ)) := by
      have h6 : ∀ (k : ℕ), 3 ≤ k → 
        ∑ i ∈ Finset.Icc 3 k, (i : ℝ) / ((i - 2).factorial + (i - 1).factorial + i.factorial) = (1 / 2 : ℝ) - (1 / (k.factorial : ℝ)) := by
        intro k hk
        induction k with
        | zero =>
          exfalso 
          omega
        | succ k ih =>
          cases k with
          | zero =>
            exfalso 
            omega
          | succ k =>
            cases k with
            | zero =>
              exfalso 
              omega
            | succ k =>
              cases k with
              | zero =>
                norm_num [Finset.sum_Icc_succ_top, Nat.factorial] at *
              | succ k =>
                rw [Finset.sum_Icc_succ_top (by omega)]
                rw [ih (by omega)]
                field_simp [Nat.factorial]
                <;> ring_nf <;> norm_num
      specialize h6 n hn
      simpa using h6
    have h4 : (1 / 2 : ℝ) - (1 / (n.factorial : ℝ)) < (1 / 2 : ℝ) := by
      have h7 : (1 / (n.factorial : ℝ)) > 0 := by
        apply div_pos
        norm_num
        have h8 : n.factorial > 0 := by
          apply Nat.factorial_pos
        have h8' : (n.factorial : ℝ) > 0 := by
          exact_mod_cast h8
        linarith
      linarith
    linarith [h5, h4]
  linarith