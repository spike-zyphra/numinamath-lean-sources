import Mathlib

theorem number_theory_291581 : IsGreatest {k | 7^k ∣ ∏ i ∈ Finset.range 1000, (i + 1)} 164 := by 
  constructor
  · -- Prove that 164 is indeed in the set
    native_decide
  · -- Prove that for any k in the set, k ≤ 164
    intro k
    intro hk
    have h7k : 7^k ∣ ∏ i in Finset.range 1000, (i + 1) := hk
    have h6 : k ≤ 164 := by
      by_contra h
      push_neg at h
      have h7k' : k ≥ 165 := by omega
      have h2 : ¬ (7^165 ∣ ∏ i in Finset.range 1000, (i + 1)) := by
        native_decide
      have h3 : 7 ^ 165 ∣ ∏ i in Finset.range 1000, (i + 1) := by
        have h4 : 7 ^ 165 ∣ 7 ^ k := by 
          exact pow_dvd_pow _ (by omega)
        have h5 : 7 ^ k ∣ ∏ i in Finset.range 1000, (i + 1) := h7k
        exact dvd_trans h4 h5
      exact h2 h3
    linarith
  all_goals try { linarith }