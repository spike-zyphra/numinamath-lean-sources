import Mathlib

theorem number_theory_5990 : IsGreatest {k | 2^k ∣ Nat.factorial 623} 616 ∧
    IsGreatest {k | 3^k ∣ Nat.factorial 623} 308 ∧
    IsGreatest {k | 6^k ∣ Nat.factorial 623} 308 ∧
    IsGreatest {k | 12^k ∣ Nat.factorial 623} 308 ∧
    IsGreatest {k | 70^k ∣ Nat.factorial 623} 102 := by
  constructor
  · -- Greatest for 2
    constructor
    · -- Show that 616 is in the set
      native_decide
    · -- Show it's greatest
      intro k hk
      have h : 2^k ∣ Nat.factorial 623 := hk
      by_contra h'
      push_neg at h'
      have h1 : k ≥ 617 := by omega
      have h2 : ¬ (2^617 ∣ Nat.factorial 623) := by
        native_decide
      have h3 : 2^617 ∣ 2^k := by
        apply pow_dvd_pow _ (by omega)
      have h4 : 2^k ∣ Nat.factorial 623 := hk
      have h5 : 2^617 ∣ Nat.factorial 623 := by
        exact dvd_trans h3 h4
      exact h2 h5
  constructor
  · -- Greatest for 3
    constructor
    · -- Show that 308 is in the set
      native_decide
    · -- Show it's greatest
      intro k hk
      have h : 3^k ∣ Nat.factorial 623 := hk
      by_contra h'
      push_neg at h'
      have h1 : k ≥ 309 := by omega
      have h2 : ¬ (3^309 ∣ Nat.factorial 623) := by
        native_decide
      have h3 : 3^309 ∣ 3^k := by
        apply pow_dvd_pow _ (by omega)
      have h4 : 3^k ∣ Nat.factorial 623 := hk
      have h5 : 3^309 ∣ Nat.factorial 623 := by
        exact dvd_trans h3 h4
      exact h2 h5
  constructor
  · -- Greatest for 6
    constructor
    · -- Show that 308 is in the set
      native_decide
    · -- Show it's greatest
      intro k hk
      have h : 6^k ∣ Nat.factorial 623 := hk
      by_contra h'
      push_neg at h'
      have h1 : k ≥ 309 := by omega
      have h2 : ¬ (6^309 ∣ Nat.factorial 623) := by
        native_decide
      have h3 : 6^309 ∣ 6^k := by
        apply pow_dvd_pow _ (by omega)
      have h4 : 6^k ∣ Nat.factorial 623 := hk
      have h5 : 6^309 ∣ Nat.factorial 623 := by
        exact dvd_trans h3 h4
      exact h2 h5
  constructor
  · -- Greatest for 12
    constructor
    · -- Show that 308 is in the set
      native_decide
    · -- Show it's greatest
      intro k hk
      have h : 12^k ∣ Nat.factorial 623 := hk
      by_contra h'
      push_neg at h'
      have h1 : k ≥ 309 := by omega
      have h2 : ¬ (12^309 ∣ Nat.factorial 623) := by
        native_decide
      have h3 : 12^309 ∣ 12^k := by
        apply pow_dvd_pow _ (by omega)
      have h4 : 12^k ∣ Nat.factorial 623 := hk
      have h5 : 12^309 ∣ Nat.factorial 623 := by
        exact dvd_trans h3 h4
      exact h2 h5
  · -- Greatest for 70
    constructor
    · -- Show that 102 is in the set
      native_decide
    · -- Show it's greatest
      intro k hk
      have h : 70^k ∣ Nat.factorial 623 := hk
      by_contra h'
      push_neg at h'
      have h1 : k ≥ 103 := by omega
      have h2 : ¬ (70^103 ∣ Nat.factorial 623) := by
        native_decide
      have h3 : 70^103 ∣ 70^k := by
        apply pow_dvd_pow _ (by omega)
      have h4 : 70^k ∣ Nat.factorial 623 := hk
      have h5 : 70^103 ∣ Nat.factorial 623 := by
        exact dvd_trans h3 h4
      exact h2 h5