import Mathlib

theorem number_theory_94930 : IsGreatest {k | 2^k ∣ 10^1002 - 4^501} 1005 := by 
  constructor 
  · -- Prove 1005 is in the set 
    native_decide 
  · -- Prove no value greater than 1005 is in the set 
    intro k hk 
    have h : 2^k ∣ 10^1002 - 4^501 := hk 
    have h1 : k ≤ 1005 := by 
      by_contra h2 
      push_neg at h2 
      have h3 : k ≥ 1006 := by linarith 
      have h4 : ¬ (2^1006 ∣ 10^1002 - 4^501) := by 
        native_decide 
      have h5 : 2^1006 ∣ 2^k := by 
        apply pow_dvd_pow _ (by linarith 
        ) 
      have h6 : 2^1006 ∣ 10^1002 - 4^501 := by 
        exact dvd_trans h5 h 
      exact h4 h6 
    linarith