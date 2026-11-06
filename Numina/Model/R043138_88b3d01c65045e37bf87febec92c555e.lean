import Mathlib

theorem number_theory_14652 : IsGreatest {k | 0 < k ∧ (2004^k : ℤ) ∣ Nat.factorial 2004} 12 := by
  constructor
  · -- Show that 12 is in the set.
    constructor
    · norm_num
    · -- Show that 2004^12 divides 2004!
      native_decide
  · -- Show that 12 is greatest in the set.
    intro k ⟨hk_pos, hk_div⟩
    by_contra h
    push_neg at h
    have h1 : k ≥ 13 := by omega
    have h2 : ¬ ((2004^13) : ℤ) ∣ Nat.factorial 2004 := by
      native_decide
    have h4 : (2004 : ℤ) ^ k ∣ (Nat.factorial 2004 : ℤ) := by
      exact_mod_cast hk_div
    have h5 : (2004 : ℤ) ^ 13 ∣ (2004 : ℤ) ^ k := by
      apply pow_dvd_pow _ (by omega)
    have h6 : (2004 : ℤ) ^ 13 ∣ (Nat.factorial 2004 : ℤ) := by
      exact dvd_trans h5 h4
    have h7 : ¬ ((2004 : ℤ) ^ 13) ∣ (Nat.factorial 2004 : ℤ) := by
      simpa using h2
    contradiction