import Mathlib

theorem number_theory_98498 : IsGreatest {n | 0 < n ∧ (10 ^ n : ℕ) ∣ Nat.factorial 1005} 250 := by
  constructor
  · -- Show 250 is in the set.
    constructor
    · norm_num 
    · -- Show that 10^250 divides 1005!
      native_decide 
  · -- Show no number greater than 250 is in the set
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    -- Assume 10^n divides 1005! with n > 250.
    -- We'll derive a contradiction.
    have h1 : n > 250 := h
    -- Let's show 10^251 does not divide 1005!
    have h2 : ¬ (10 ^ 251 : ℕ) ∣ Nat.factorial 1005 := by
      native_decide
    -- But since n > 250, we have 10^251 divides 10^n.
    have h3 : (10 ^ 251 : ℕ) ∣ 10 ^ n := by
      have h4 : 251 ≤ n := by omega 
      exact pow_dvd_pow _ (by omega)
    -- By transitivity, 10^251 divides 1005!, contradiction.
    have h4 : (10 ^ 251 : ℕ) ∣ Nat.factorial 1005 := by 
      exact Nat.dvd_trans h3 hn_div
    exact h2 h4