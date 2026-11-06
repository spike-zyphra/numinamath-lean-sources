import Mathlib

theorem number_theory_93140 : IsGreatest {n | 0 < n ∧ (5^n : ℤ) ∣ Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100} 26 := by
  constructor
  · -- Show 26 is in the set
    constructor
    · norm_num
    · native_decide
  · -- Show that if n is in the set, then n ≤ 26
    intro n hn
    rcases hn with ⟨hn_pos, h⟩
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 27 := by omega
    have h3 : ¬ ( (5 ^ 27 : ℤ) ∣ Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 ) := by
      native_decide
    have h4 : n ≥ 27 := by omega
    have h5 : (5 ^ 27 : ℤ) ∣ (5 ^ n : ℤ) := by 
      apply pow_dvd_pow _ (by omega)
    have h6 : (5 ^ 27 : ℤ) ∣ Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 := by
      exact dvd_trans h5 h
    exact h3 h6