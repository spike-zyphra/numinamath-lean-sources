import Mathlib

open Nat

theorem number_theory_1622 : IsGreatest {k : ℕ | 18 ^ k ∣ 100 !} 24 := by
  constructor 
  · -- Show that 24 is indeed in the set
    native_decide
  · -- Show that any k in the set is ≤ 24
    intro k hk
    have h : 18 ^ k ∣ 100 ! := hk
    by_contra h'
    push_neg at h'
    have h2 : k ≥ 25 := by omega
    have h3 : ¬ (18 ^ 25 ∣ 100 !) := by 
      native_decide
    have h4 : 18 ^ 25 ∣ 18 ^ k := by
      apply pow_dvd_pow _ (by omega)
    have h5 : 18 ^ 25 ∣ 100 ! := by 
      exact dvd_trans h4 h
    contradiction