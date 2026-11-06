import Mathlib

set_option maxRecDepth 100000
theorem number_theory_608191: IsGreatest {n: ℕ | 2007 ^ n ∣ Nat.factorial 2007} 9 := by
  constructor
  · -- Show 9 is in the set
    native_decide
  · -- Show no larger element is in the set
    intro n hn
    have h : 2007 ^ n ∣ Nat.factorial 2007 := hn
    by_contra h1
    push_neg at h1
    have h2 : n ≥ 10 := by omega
    have h3 : ¬ (2007 ^ 10 ∣ Nat.factorial 2007) := by native_decide
    have h4 : 2007 ^ 10 ∣ 2007 ^ n := by
      apply pow_dvd_pow _ (by omega)
    have h5 : 2007 ^ 10 ∣ Nat.factorial 2007 := by
      exact dvd_trans h4 h
    exact h3 h5