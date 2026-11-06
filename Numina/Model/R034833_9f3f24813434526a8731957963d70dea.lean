import Mathlib

theorem number_theory_197485 : IsGreatest {a | 0 ≤ a ∧ (Nat.factorial 50) % (2^a) = 0} 47 := by
  constructor
  · -- Show that 47 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Show that 47 is greatest in the set
    intro a
    intro ha
    rcases ha with ⟨ha_nonneg, h⟩
    by_contra h'
    push_neg at h'
    have h1 : a > 47 := by omega
    have h2 : (Nat.factorial 50) % (2 ^ 48) ≠ 0 := by
      native_decide
    have h3 : a ≥ 48 := by omega
    -- Show that $2^{48}$ does not divide $50!$.
    have h4 : (Nat.factorial 50) % (2 ^ 48) = 0 := by
      have h5 : (2 ^ 48) ∣ (2 ^ a) := by
        apply pow_dvd_pow
        all_goals omega
      have h6 : (2 ^ a) ∣ (Nat.factorial 50) := by
        exact Nat.dvd_of_mod_eq_zero h
      have h7 : (2 ^ 48) ∣ (Nat.factorial 50) := by
        exact dvd_trans h5 h6
      exact Nat.mod_eq_zero_of_dvd h7
    contradiction