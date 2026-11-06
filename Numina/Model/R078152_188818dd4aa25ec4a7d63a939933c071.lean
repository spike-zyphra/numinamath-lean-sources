import Mathlib

theorem number_theory_95496 : IsGreatest {t:ℕ | t ∣ 2 * 3 * 4 * 5 * 6 ∧ t ∣ 1 * 3 * 4 * 5 * 6 ∧ t ∣ 1 * 2 * 4 * 5 * 6 ∧ t ∣ 1 * 2 * 3 * 5 * 6 ∧ t ∣ 1 * 2 * 3 * 4 * 6 ∧ t ∣ 1 * 2 * 3 * 4 * 5} 12 := by 
  constructor
  · -- Show that 12 is in the set
    constructor
    · -- Check divisibility of 2 * 3 * 4 * 5 * 6 by 12
      norm_num
    constructor
    · -- Check divisibility of 1 * 3 * 4 * 5 * 6 by 12
      norm_num
    constructor
    · -- Check divisibility of 1 * 2 * 4 * 5 * 6 by 12
      norm_num
    constructor
    · -- Check divisibility of 1 * 2 * 3 * 5 * 6 by 12
      norm_num
    constructor
    · -- Check divisibility of 1 * 2 * 3 * 4 * 6 by 12
      norm_num
    · -- Check divisibility of 1 * 2 * 3 * 4 * 5 by 12
      norm_num
  · -- Show that 12 is greatest in the set
    intro t ht 
    rcases ht with ⟨h1, h2, h3, h4, h5, h6⟩
    have h7 : t ∣ 12 := by
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4) h5) h6
    have h8 : t ≤ 12 := by 
      exact Nat.le_of_dvd (by norm_num) h7
    linarith