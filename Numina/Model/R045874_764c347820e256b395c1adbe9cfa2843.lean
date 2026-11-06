import Mathlib

theorem number_theory_13693 : IsGreatest {n | 0 < n ∧ (Nat.factorial 100) % (6 ^ n) = 0} 48 := by
  constructor
  · -- Show 48 is in the set
    constructor
    · -- Show 48 > 0
      norm_num
    · -- Show Nat.factorial 100 % 6 ^ 48 = 0
      native_decide
  · -- Show no number greater than 48 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 49 := by omega
    have h2 : (Nat.factorial 100) % (6 ^ n) ≠ 0 := by
      have h3 : n ≥ 49 := h1
      have h4 : (6 ^ 49) ∣ (6 ^ n) := by
        apply pow_dvd_pow _ (by omega)
      have h5 : ¬ (6 ^ 49 ∣ (Nat.factorial 100)) := by
        native_decide
      have h6 : (6 ^ n) ∣ (Nat.factorial 100) := by
        have h7 : (Nat.factorial 100) % (6 ^ n) = 0 := hn_div
        exact Nat.dvd_of_mod_eq_zero h7
      have h7 : (6 ^ 49) ∣ (Nat.factorial 100) := by
        exact dvd_trans h4 h6
      contradiction
    contradiction