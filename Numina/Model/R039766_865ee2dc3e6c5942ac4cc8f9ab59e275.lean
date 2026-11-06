import Mathlib

open Real
open scoped BigOperators

theorem number_theory_288432 :
  IsLeast {x : ℝ | ∃ n : ℕ, n ∈ Finset.Icc 100 999 ∧ x = n / (Nat.digits 10 n).sum} (199 / 19) := by 
  constructor
  · -- Show 199/19 is in the set
    use 199
    constructor
    · -- Show 199 is in [100, 999]
      exact Finset.mem_Icc.mpr ⟨by norm_num, by norm_num⟩
    · -- Show the value of the expression at 199
      norm_num
  · -- Show it's minimal
    intro x hx
    rcases hx with ⟨n, hn, hx⟩
    rw [Finset.mem_Icc] at hn
    rcases hn with ⟨hn1, hn2⟩
    by_contra h
    push_neg at h
    have h3 : (n : ℝ) / (Nat.digits 10 n).sum < (199 / 19 : ℝ) := by 
      linarith [hx, h]
    interval_cases n <;> norm_num at h3 ⊢
    all_goals
      contradiction