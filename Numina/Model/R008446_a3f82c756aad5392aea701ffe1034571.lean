import Mathlib

open Nat

theorem number_theory_42854 : IsLeast {n : ℕ | 0 < n ∧ 1000 ∣ (2^n + 5^n - n)} 797 := by
  constructor
  · -- Show 797 is in the set
    constructor
    · norm_num  -- Show that 0 < 797
    · norm_num  -- Show that 1000 divides (2^797 + 5^797 - 797)
  · -- Show that for any n in the set, 797 ≤ n
    intro n hn
    have h1 : 0 < n := (hn.left)
    have h2 : 1000 ∣ (2^n + 5^n - n) := hn.right
    by_contra h
    push_neg at h
    have h3 : n ≤ 796 := by omega
    interval_cases n <;> norm_num at h2 <;> omega