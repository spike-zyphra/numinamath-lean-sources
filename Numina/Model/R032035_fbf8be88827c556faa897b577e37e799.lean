import Mathlib

theorem number_theory_23494 : IsGreatest {n | 0 < n ∧ (15^n : ℤ) ∣ Nat.factorial 942} 233 := by
  constructor 
  · -- Show that 233 is in the set 
    constructor 
    · -- Show that 233 > 0 
      norm_num 
    · -- Show that 15^233 divides 942!
      native_decide 
  · -- Show that if n in the set, then n ≤ 233 
    intro n hn 
    rcases hn with ⟨hn_pos, hn_div⟩ 
    by_contra h 
    push_neg at h 
    have h1 : n ≥ 234 := by omega 
    -- Now n ≥ 234, we derive a contradiction
    have h14 : n ≥ 234 := h1 
    have h24 : (15 ^ 234 : ℤ) ∣ (15 ^ n : ℤ) := by 
      apply pow_dvd_pow _ (by omega) 
    -- So 15^234 divides Nat.factorial 942
    have h34 : (15 ^ 234 : ℤ) ∣ (Nat.factorial 942 : ℤ) := by 
      exact dvd_trans h24 hn_div 
    -- We can derive 5^234 divides Nat.factorial 942
    -- First, show 5^234 divides 15^234
    have h354 : (5 ^ 234 : ℤ) ∣ (15 ^ 234 : ℤ) := by 
      norm_num 
    -- Now by transitivity, 5^234 divides Nat.factorial 942
    have h354' : (5 ^ 234 : ℤ) ∣ (Nat.factorial 942 : ℤ) := by 
      exact dvd_trans h354 h34 
    -- This is a contradiction because 5^234 does not divide 942!
    have h44 : ¬ ( (5 : ℤ) ^ 234 ) ∣ ( (Nat.factorial 942 : ℤ) ) := by 
      native_decide 
    exfalso 
    exact h44 h354'