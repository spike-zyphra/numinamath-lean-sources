import Mathlib

theorem number_theory_51045 :
    ∃! n, Odd n ∧ 500 < n ∧ n < 1000 ∧ n % 25 = 6 ∧ n % 9 = 7 := by 
  use 781
  constructor
  · -- Show that 781 is odd and satisfy the constraints.
    constructor
    · -- Show that 781 is odd
      exact Nat.odd_iff.mpr (by norm_num)
    constructor
    · -- Show that 500 < 781
      norm_num
    constructor
    · -- Show that 781 < 1000
      norm_num
    constructor
    · -- Show that 781 % 25 = 6
      norm_num
    · -- Show that 781 % 9 = 7
      norm_num
  · -- Show that the witness is unique
    intro n hn
    rcases hn with ⟨hn_odd, hn1, hn2, hn_mod_25, hn_mod_9⟩
    have h1 : n > 500 := by nlinarith
    have h2 : n < 1000 := by nlinarith
    interval_cases n <;> norm_num [Nat.odd_iff] at hn_odd hn_mod_25 hn_mod_9 ⊢
    <;> all_goals omega