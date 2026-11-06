import Mathlib

theorem number_theory_15987 : IsGreatest { d : ℕ | d ∣ 2 * 3 * 4 * 5 * 6 ∧ d ∣ 1 * 3 * 4 * 5 * 6 ∧ d ∣ 1 * 2 * 4 * 5 * 6 ∧ d ∣ 1 * 2 * 3 * 5 * 6 ∧ d ∣ 1 * 2 * 3 * 4 * 6 ∧ d ∣ 1 * 2 * 3 * 4 * 5 } 12 := by
  constructor
  · -- Show that 12 is in the set
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · -- Show that if d is in the set, then d ≤ 12
    intro d
    intro h
    rcases h with ⟨h1, h2, h3, h4, h5, h6⟩
    have h7 : d ∣ 12 := by 
      exact Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd (Nat.dvd_gcd h1 h2) h3) h4) h5) h6
    have h8 : d ≤ 12 := by 
      exact Nat.le_of_dvd (by norm_num) h7
    linarith