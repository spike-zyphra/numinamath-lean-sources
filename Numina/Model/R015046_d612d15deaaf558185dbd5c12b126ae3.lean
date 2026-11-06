import Mathlib

theorem number_theory_6064 : IsGreatest {k | 10^k ∣ Nat.factorial 420} 103 := by
  constructor
  · -- Show that 103 is in the set
    native_decide
  · -- Show that no k > 103 is in the set
    intro k hk
    have h : 10 ^ k ∣ Nat.factorial 420 := by
      simpa using hk
    by_contra h'
    push_neg at h'
    have h2 : k ≥ 104 := by omega
    have h3 : ¬ (10 ^ 104 ∣ Nat.factorial 420) := by
      native_decide
    have h4 : 10 ^ 104 ∣ Nat.factorial 420 := by
      have h5 : 10 ^ k ∣ Nat.factorial 420 := h
      have h6 : k ≥ 104 := h2
      have h7 : 10 ^ 104 ∣ 10 ^ k := by 
        exact pow_dvd_pow _ (by linarith)
      have h8 : 10 ^ 104 ∣ Nat.factorial 420 := by 
        exact dvd_trans h7 h5
      exact h8
    exact h3 h4