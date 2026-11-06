import Mathlib

theorem number_theory_319026 : IsGreatest {n | 0 < n ∧ (5^n : ℤ) ∣ Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 ∧ ¬(5^(n + 1) : ℤ) ∣ Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100} 26 := by 
  constructor
  · -- Show 26 is in the set
    constructor
    · -- Show 0 < 26
      norm_num 
    constructor
    · -- Show that 5^26 divides the sum
      native_decide
    · -- Show that 5^27 does not divide the sum
      native_decide
  · -- Assume n is in the set, we need to prove n ≤ 26
    intro n hn
    rcases hn with ⟨hn_pos, hn_div, hn_not_div⟩
    by_contra h
    push_neg at h
    -- Now assume h: n > 26, so n ≥ 27
    have h1 : n ≥ 27 := by linarith 
    have h2 : (5 ^ 27 : ℤ) ∣ 5 ^ n := by 
      apply pow_dvd_pow _ (by linarith)
    have h3 : (5 ^ 27 : ℤ) ∣ (Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 : ℤ) := by 
      have h4 : (5 ^ n : ℤ) ∣ (Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 : ℤ) := hn_div 
      have h5 : (5 ^ 27 : ℤ) ∣ (5 ^ n : ℤ) := by 
        apply pow_dvd_pow _ (by linarith)
      have h6 : ((5 ^ 27 : ℤ) : ℤ) ∣ (Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 : ℤ) := by 
        exact dvd_trans h5 h4 
      exact h6 
    have h4 : ¬ (5 ^ 27 : ℤ) ∣ (Nat.factorial 98 + Nat.factorial 99 + Nat.factorial 100 : ℤ) := by 
      native_decide 
    contradiction