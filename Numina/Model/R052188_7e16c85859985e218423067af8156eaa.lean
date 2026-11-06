import Mathlib

theorem number_theory_243445 : IsGreatest {n | 0 < n ∧ (39^n : ℕ) ∣ Nat.factorial 39} 3 := by
  constructor
  · -- Prove 3 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Prove for any n in the set, n ≤ 3
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    have h1 : n ≥ 4 := by omega
    have h2 : ¬ (39 ^ 4 : ℕ) ∣ Nat.factorial 39 := by
      native_decide
    have h3 : (39 ^ n : ℕ) ∣ Nat.factorial 39 := hn_div
    have h4 : (39 ^ 4 : ℕ) ∣ (39 ^ n : ℕ) := by 
      apply pow_dvd_pow _ (by omega)
    have h5 : (39 ^ 4 : ℕ) ∣ Nat.factorial 39 := by 
      exact dvd_trans h4 h3
    exact h2 h5