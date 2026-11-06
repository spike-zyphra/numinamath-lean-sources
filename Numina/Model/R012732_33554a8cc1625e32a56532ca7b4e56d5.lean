import Mathlib

theorem number_theory_34942 : IsGreatest {n | 2^n ∣ 5^256 - 1} 10 := by

  constructor
  · -- First part: Show 10 is in the set
    native_decide
  · -- Second part: Show that if n in the set then n <= 10
    intro n hn
    have h : 2^n ∣ 5^256 - 1 := hn
    by_contra h1
    push_neg at h1
    have h11 : n ≥ 11 := by omega
    have h2 : n ≥ 11 := h11
    have h3 : ¬ (2 ^ 11 ∣ 5^256 - 1) := by
      native_decide
    have h4 : 2 ^ 11 ∣ 5 ^ 256 - 1 := by
      have h5 : 2 ^ n ∣ 5 ^ 256 - 1 := h
      have h6 : 2 ^ 11 ∣ 2 ^ n := by
        apply pow_dvd_pow _ (by linarith)
      have h7 : 2 ^ 11 ∣ 5 ^ 256 - 1 := by
        exact dvd_trans h6 h5
      exact h7
    contradiction