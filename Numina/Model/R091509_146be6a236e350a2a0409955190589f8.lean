import Mathlib

theorem number_theory_192788 : IsGreatest {k | 2007 ^ k ∣ Nat.factorial 2007} 9 := by
  constructor
  · -- Show that 9 is in the set
    native_decide
  · -- Show that any k in the set is at most 9
    intro k hk
    have h : 2007 ^ k ∣ Nat.factorial 2007 := hk
    by_contra h'
    push_neg at h'
    have h1 : k ≥ 10 := by omega
    have h2 : 2007 ^ 10 ∣ 2007 ^ k := by
      apply pow_dvd_pow _ (by linarith)
    have h3 : 2007 ^ 10 ∣ Nat.factorial 2007 := by 
      exact Nat.dvd_trans h2 h
    have h4 : ¬(2007 ^ 10 ∣ Nat.factorial 2007) := by 
      native_decide
    exact h4 h3