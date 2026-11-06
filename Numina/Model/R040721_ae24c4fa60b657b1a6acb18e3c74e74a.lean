import Mathlib

open Nat


theorem imo_23769
    (rg : Finset ℤ)
    (h_defrg : rg = Finset.Icc 1 100)
    (s : Set ℤ)
    (h_defs : s = {v : ℤ | ∃ m ∈ rg, ∃ n ∈ rg, (n ^ 2 - m * n - m ^ 2) ^ 2 = 1 ∧ m ^ 2 + n ^ 2 = v})
    : IsGreatest s (55 ^ 2 + 89 ^ 2) := by 
  rw [h_defs]
  constructor
  · -- Show 55^2 + 89^2 in s
    use 55, by rw [h_defrg]; native_decide, 89, by rw [h_defrg]; native_decide
    all_goals norm_num 
  · -- Show no value greater than 55^2 + 89^2 in s
    intro v hv
    rcases hv with ⟨m, hm, n, hn, h1, h2⟩
    rw [h_defrg] at hm hn
    simp [Finset.mem_Icc] at hm hn
    rcases hm with ⟨h3, h4⟩
    rcases hn with ⟨h5, h6⟩
    interval_cases m <;> interval_cases n <;> omega