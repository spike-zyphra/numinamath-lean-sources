import Mathlib

theorem number_theory_70563 : IsGreatest {k | 7^k ∣ ∏ i ∈ Finset.range 50, (i + 1)^2} 16 := by 
  constructor 
  · -- Show 16 is in the set
    native_decide 
  · -- Show that if k ∈ {k | 7^k ∣ ∏ i ∈ Finset.range 50, (i + 1)^2}, then k ≤ 16
    intro k hk
    have h : 7^k ∣ ∏ i ∈ Finset.range 50, (i + 1)^2 := by 
      simpa using hk 
    have h2 : k ≤ 16 := by 
      by_contra h'
      push_neg at h'
      have h3 : k ≥ 17 := by omega
      have h4 : ¬ (7^17 ∣ ∏ i ∈ Finset.range 50, (i + 1)^2) := by 
        native_decide 
      have h5 : 7^17 ∣ ∏ i ∈ Finset.range 50, (i + 1)^2 := by 
        have h6 : k ≥ 17 := by linarith 
        have h7 : 7^17 ∣ 7^k := by 
          exact pow_dvd_pow _ (by linarith) 
        exact dvd_trans h7 h 
      contradiction 
    linarith