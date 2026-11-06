import Mathlib

open Finset

theorem number_theory_134442 : IsGreatest {k | 10^k ∣ ∏ i ∈ range 100, (100 - i)} 24 := by
  constructor
  · -- Show that 24 is indeed in the set
    native_decide
  · -- Show that if a natural number is in the set, then it's at most 24
    intro k hk
    have h : 10^k ∣ ∏ i ∈ range 100, (100 - i) := hk
    have h2 : k ≤ 24 := by
      by_contra h2
      push_neg at h2
      have h3 : k ≥ 25 := by omega
      have h4 : ¬ (10^25 ∣ ∏ i ∈ range 100, (100 - i)) := by
        native_decide
      have h5 : 10^25 ∣ 10^k := by
        apply pow_dvd_pow _ (by linarith)
      have h6 : 10^k ∣ ∏ i ∈ range 100, (100 - i) := h
      have h7 : 10^25 ∣ ∏ i ∈ range 100, (100 - i) := by
        apply dvd_trans h5 h6
      contradiction
    linarith