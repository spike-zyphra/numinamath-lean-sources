import Mathlib

theorem number_theory_15865 : IsGreatest {k : ℕ | 20 ∣ k ∧ k % 26 = 4 ∧ k < 1000} 940 := by
  constructor
  · -- Show 940 is in the set
    show 20 ∣ 940 ∧ 940 % 26 = 4 ∧ 940 < 1000
    constructor
    · -- Show 20 divides 940
      norm_num
    constructor
    · -- Show 940 % 26 = 4
      norm_num
    all_goals norm_num
  · -- Show that for all k in the set, k ≤ 940
    intro k hk
    rcases hk with ⟨h20, h26, hk1⟩
    by_contra h
    push_neg at h
    have h1 : k ≥ 941 := by omega
    have h2 : k < 1000 := by linarith
    interval_cases k <;> norm_num at h20 h26 <;> try { contradiction } <;> omega
    all_goals omega
    all_goals contradiction
    all_goals omega