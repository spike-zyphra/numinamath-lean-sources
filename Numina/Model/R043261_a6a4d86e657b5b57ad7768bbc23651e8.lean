import Mathlib

theorem number_theory_320993 :
    IsGreatest {n : ℕ | 2 ^ n ∣ 2007 ^ 2048 - 1} 14 := by
  constructor
  · -- First, show that 14 is in the set
    native_decide
  · -- Second, show that 14 is greatest in the set
    intro n hn
    have h : 2 ^ n ∣ 2007 ^ 2048 - 1 := hn
    by_contra h'
    push_neg at h'
    -- Assume n > 14, we need to derive a contradiction
    have h15 : 2 ^ 15 ∣ 2 ^ n := by
      apply pow_dvd_pow _ (by omega)
    have h16 : 2 ^ 15 ∣ 2007 ^ 2048 - 1 := by
      exact dvd_trans h15 h
    -- Show that $2^15$ does not divide the expression
    have h17 : ¬ (2 ^ 15 ∣ 2007 ^ 2048 - 1) := by
      native_decide
    exact h17 h16