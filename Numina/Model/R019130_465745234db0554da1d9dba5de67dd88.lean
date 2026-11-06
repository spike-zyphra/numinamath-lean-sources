import Mathlib

theorem number_theory_202057 : IsGreatest {k | 0 < k ∧ 10 ^ k ∣ Nat.factorial 90} 21 := by
  constructor
  · -- Show 21 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Show that 21 is greatest in the set
    intro k hk
    rcases hk with ⟨hk_pos, hk_div⟩
    by_contra h
    push_neg at h
    have h2 : k ≥ 22 := by omega
    -- Show that $10^22$ does not divide $90!$
    have h3 : ¬ (10 ^ 22 ∣ Nat.factorial 90) := by
      native_decide
    -- Prove a contradiction
    have h4 : 10 ^ 22 ∣ 10 ^ k := by
      apply pow_dvd_pow _ (by omega)
    have h5 : 10 ^ 22 ∣ Nat.factorial 90 := by
      exact dvd_trans h4 hk_div
    contradiction