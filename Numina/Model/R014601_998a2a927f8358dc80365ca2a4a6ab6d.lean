import Mathlib

theorem number_theory_126844 : IsGreatest {n | 0 < n ∧ 10^n ∣ Nat.factorial 1005} 250 := by
  constructor
  · -- Show 250 is in the set
    constructor
    · norm_num
    · -- Show 10^250 divides 1005!
      native_decide
  · -- Show that no integer greater than 250 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h251 : n ≥ 251 := by omega
    have h251_div : 10 ^ 251 ∣ 10 ^ n := by
      apply pow_dvd_pow _ (by omega)
    have h1005 : 10 ^ 251 ∣ Nat.factorial 1005 := by 
      exact dvd_trans h251_div hn_div
    -- Show that 10^251 does not divide 1005!
    have h1005' : ¬ (10 ^ 251 ∣ Nat.factorial 1005) := by
      native_decide
    exact h1005' h1005