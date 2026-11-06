import Mathlib

theorem number_theory_288413 : IsGreatest {n | 0 < n ∧ 7^n ∣ Nat.factorial 200 / (Nat.factorial 90 * Nat.factorial 30)} 15 := by 
  constructor
  · -- Show that 15 is in the set 
    constructor
    · norm_num 
    · native_decide
  · -- Show that any n in the set is ≤ 15
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    have h : n ≤ 15 := by 
      by_contra h'
      push_neg at h'
      have h1 : n ≥ 16 := by omega 
      have h2 : ¬ (7 ^ 16 ∣ Nat.factorial 200 / (Nat.factorial 90 * Nat.factorial 30)) := by 
        native_decide
      have h3 : 7 ^ 16 ∣ Nat.factorial 200 / (Nat.factorial 90 * Nat.factorial 30) := by 
        have h4 : 7 ^ 16 ∣ 7 ^ n := by 
          apply pow_dvd_pow _ (by omega)
        have h5 : 7 ^ n ∣ Nat.factorial 200 / (Nat.factorial 90 * Nat.factorial 30) := hn_div
        exact Dvd.dvd.trans h4 h5 
      contradiction 
    linarith 
    all_goals 
      linarith