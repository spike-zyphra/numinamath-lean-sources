import Mathlib
import Aesop

open BigOperators Real Nat Topology Rat

/- The positive integer value of $n$ that makes ${{2}^{n}}+256$ a perfect square is ___          ___. -/
theorem number_theory_258 :
  IsLeast {n | 0 < n ∧ ∃ k, (2^n + 256) = k^2} 11 := by
  constructor
  · -- Show 11 is in the set.
    constructor
    · norm_num
    · use 48
      all_goals norm_num
  · -- Show that 11 is the smallest such number.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, hk⟩⟩
    by_contra h'
    push_neg at h'
    interval_cases n <;> try { 
      norm_num at hk
      all_goals
      have h1 : k > 0 := by nlinarith
      have h2 : k ≤ 55 := by nlinarith
      interval_cases k <;> omega
    }