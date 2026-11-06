import Mathlib

theorem number_theory_189774 : IsGreatest {n | 0 < n ∧ (2^n : ℤ) ∣ 3^512 - 1} 11 := by
  constructor
  · -- Show that 11 is in the set
    constructor
    · -- Show that 11 > 0
      norm_num
    · -- Show that 2^11 divides 3^512 - 1
      native_decide
  · -- Show that any element in the set is ≤ 11
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    -- Suppose n is in the set, so 2^n divides 3^512 - 1
    -- We need to show n ≤ 11
    by_contra h
    push_neg at h
    -- Now h: n > 11
    have h6 : n ≥ 12 := by omega
    -- Show that 2^12 divides 2^n
    have h7 : (2 : ℤ) ^ 12 ∣ (2 : ℤ) ^ n := by
      exact pow_dvd_pow _ (by omega)
    -- Since 2^n divides 3^512 - 1 and 2^12 divides 2^n,
    -- we get that 2^12 divides 3^512 - 1
    have h8 : (2 : ℤ) ^ 12 ∣ (3 ^ 512 - 1 : ℤ) := by
      exact dvd_trans h7 hn_div
    -- Show that 2^12 does not divide 3^512 - 1
    have h9 : ¬ ((2 : ℤ) ^ 12 ∣ (3 ^ 512 - 1 : ℤ)) := by
      native_decide
      all_goals tauto
    -- Derive a contradiction
    exfalso
    exact h9 h8