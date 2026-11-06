import Mathlib
open Nat
theorem number_theory_67783 :IsLeast {n : ℕ | 0 < n ∧ (3 ^ n) % 143 ^ 2 = 1} 195 := by
  constructor
  · -- Show that 195 is in the set
    constructor
    · norm_num
    · norm_num
  · -- Show that if n ∈ {n : ℕ | 0 < n ∧ (3 ^ n) % 143 ^ 2 = 1}, then 195 ≤ n
    intro n hn
    rcases hn with ⟨hn_pos, hn_pow⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at hn_pow <;> all_goals omega