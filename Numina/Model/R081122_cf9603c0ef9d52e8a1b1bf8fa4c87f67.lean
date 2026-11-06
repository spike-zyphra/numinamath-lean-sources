import Mathlib

theorem algebra_287274 :
    IsLeast {n : ℕ | 0 < n ∧ (n - 10) ≠ 0 ∧ Nat.gcd (n - 10) (9 * n + 11) ≠ 1} 111 := by
  constructor
  · constructor
    · norm_num
    constructor
    · norm_num
    · norm_num
  · intro n hn
    rcases hn with ⟨hn_pos, hn_ne_zero, h_gcd⟩
    by_contra h
    push_neg at h
    interval_cases n <;> norm_num at h_gcd <;> omega