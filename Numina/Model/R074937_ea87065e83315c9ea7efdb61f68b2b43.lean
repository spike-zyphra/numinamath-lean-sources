import Mathlib

open Finset

theorem number_theory_94666 : IsGreatest {n | 0 < n ∧ 2 ^ n ∣ ∏ a ∈ Set.Icc 1 20, ∏ b ∈ Set.Icc 1 20, if a < b then (b - a) else 1} 150 := by 
  constructor
  · constructor
    · norm_num
    · native_decide
  · intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 151 := by omega
    have h2 : ¬(2 ^ 151 ∣ ∏ a ∈ Set.Icc 1 20, ∏ b ∈ Set.Icc 1 20, if a < b then (b - a) else 1) := by 
      native_decide
    have h3 : 2 ^ 151 ∣ 2 ^ n := by 
      apply pow_dvd_pow _ (by omega)
    have h4 : 2 ^ 151 ∣ ∏ a ∈ Set.Icc 1 20, ∏ b ∈ Set.Icc 1 20, if a < b then (b - a) else 1 := by 
      apply dvd_trans h3 hn_div
    contradiction