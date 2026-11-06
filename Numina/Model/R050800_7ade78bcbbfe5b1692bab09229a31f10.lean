import Mathlib

theorem number_theory_311449 : IsGreatest {n | 0 < n ∧ (1998 ^ n) ∣ Nat.factorial 1999} 55 := by
  constructor
  · -- Show 55 is in the set
    constructor
    · -- Show 55 > 0
      norm_num
    · -- Show 1998^55 divides 1999!
      native_decide
  · -- Show there is no greater element in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n > 55 := h
    have h2 : ¬ (1998 ^ 56) ∣ Nat.factorial 1999 := by
      native_decide
    have h3 : n ≥ 56 := by omega
    have h4 : (1998 ^ 56) ∣ (1998 ^ n) := by
      apply pow_dvd_pow _ (by linarith)
    have h5 : (1998 ^ 56) ∣ Nat.factorial 1999 := by
      exact dvd_trans h4 hn_div
    exact h2 h5