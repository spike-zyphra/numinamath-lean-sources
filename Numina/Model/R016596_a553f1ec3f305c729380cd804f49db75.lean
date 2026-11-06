import Mathlib

open Finset

theorem number_theory_4757 : IsGreatest {n | 175^n ∣ ∏ i ∈ range 2018, (i + 1)} 251 := by
  constructor
  · -- Show 251 is in the set
    native_decide
  · -- Show there is no greater n in the set
    intro n hn
    have h1 : 175 ^ n ∣ ∏ i ∈ range 2018, (i + 1) := hn
    by_contra h2
    push_neg at h2
    have h2' : n ≥ 252 := by
      omega
    have h3 : ¬ (175 ^ 252 ∣ ∏ i ∈ range 2018, (i + 1)) := by
      native_decide
    have h5 : 175 ^ 252 ∣ ∏ i ∈ range 2018, (i + 1) := by
      have h6 : 175 ^ n ∣ ∏ i ∈ range 2018, (i + 1) := h1
      have h7 : 175 ^ 252 ∣ 175 ^ n := by
        apply pow_dvd_pow _ (by omega)
      exact dvd_trans h7 h6
    have h4 : n ≥ 252 := h2'
    exact h3 h5