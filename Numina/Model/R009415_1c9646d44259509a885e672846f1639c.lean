import Mathlib

open Nat

theorem other_115279 :
    IsLeast {n : ℕ | 0 < n ∧ 31 ∣ (5^n + n)} 30 := by
  constructor
  · -- Show 30 is in the set: 30 > 0 and 31 ∣ (5^30 + 30)
    constructor
    · -- Show 0 < 30
      norm_num
    · -- Show 31 ∣ (5^30 + 30)
      norm_num [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, pow_succ, Nat.mul_mod]
  · -- Show that 30 is the least: ∀n > 0 with 31 ∣ (5^n + n), n ≥ 30
    intro n hn
    rcases hn with ⟨hn_pos, hn_div⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_div <;> try { contradiction }