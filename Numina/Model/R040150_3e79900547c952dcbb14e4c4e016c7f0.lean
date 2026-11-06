import Mathlib

open Finset

theorem number_theory_225274 : IsGreatest {n | 2^n ∣ ∏ i ∈ range 2020, (3^(i + 1) + 1)} 3030 := by
  constructor
  · -- Show that 3030 is in the set
    native_decide
  · -- Show that for all n in the set, n ≤ 3030
    intro n hn
    have h : 2 ^ n ∣ ∏ i ∈ range 2020, (3 ^ (i + 1) + 1) := hn
    have h2 : n ≤ 3030 := by
      by_contra h3
      push_neg at h3
      have h3 : n ≥ 3031 := by omega
      have h4 : ¬ (2 ^ 3031 ∣ ∏ i ∈ range 2020, (3 ^ (i + 1) + 1)) := by
        native_decide
      have h5 : 2 ^ 3031 ∣ 2 ^ n := by
        apply pow_dvd_pow
        linarith
      have h6 : 2 ^ 3031 ∣ ∏ i ∈ range 2020, (3 ^ (i + 1) + 1) := by
        exact dvd_trans h5 h
      have h7 : ¬ (2 ^ 3031 ∣ ∏ i ∈ range 2020, (3 ^ (i + 1) + 1)) := h4
      exact h7 h6
    linarith