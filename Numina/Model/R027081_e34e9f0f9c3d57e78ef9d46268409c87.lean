import Mathlib

theorem number_theory_8155 : IsGreatest {n | (5^n : ℤ) ∣ (Nat.factorial 2006) / (Nat.factorial 1003)^2} 2 := by
  constructor
  · -- Show that 2 is in the set
    native_decide
  · -- Show that if n is in the set, then n ≤ 2
    intro n hn
    have h : (5^n : ℤ) ∣ (Nat.factorial 2006) / (Nat.factorial 1003) ^ 2 := hn
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 3 := by omega
    have h3 : ¬ (5^3 : ℤ) ∣ (Nat.factorial 2006) / (Nat.factorial 1003) ^ 2 := by
      native_decide
    have h4 : (5^3 : ℤ) ∣ (5^n : ℤ) := by
      apply pow_dvd_pow _ (by omega)
    have h5 : (5^3 : ℤ) ∣ (Nat.factorial 2006) / (Nat.factorial 1003) ^ 2 := by
      exact dvd_trans h4 h
    exact h3 h5