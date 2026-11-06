import Mathlib

theorem number_theory_7230 : IsGreatest {k | 2^k ∣ Nat.factorial 52 + Nat.factorial 24} 22 := by
  constructor
  · -- Show 22 is in the set
    native_decide
  · -- Show no greater element is in the set
    intro k hk
    have h : 2 ^ k ∣ Nat.factorial 52 + Nat.factorial 24 := hk
    have h1 : k ≤ 22 := by
      by_contra h2
      push_neg at h2
      have h23 : k ≥ 23 := by omega
      have h3 : ¬ (2 ^ 23 ∣ Nat.factorial 52 + Nat.factorial 24) := by 
        native_decide
      have h4 : 2 ^ 23 ∣ 2 ^ k := by
        apply pow_dvd_pow _ (by omega)
      have h5 : 2 ^ 23 ∣ Nat.factorial 52 + Nat.factorial 24 := by
        apply dvd_trans h4 h
      contradiction
    linarith