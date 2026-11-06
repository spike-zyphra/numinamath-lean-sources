import Mathlib

theorem number_theory_80 : IsLeast {n : ℤ | 0 < n ∧ ∃ k l, n = 15 * k + 21 * l} 3 := by
  constructor
  · -- Show that 3 is in the set.
    constructor
    · norm_num
    · -- Show specific integers k and l such that 3 = 15 * k + 21 * l
      use 3, -2
      norm_num
  · -- Show that 3 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨hn_pos, ⟨k, l, hn_eq⟩⟩
    have h1 : n = 15 * k + 21 * l := hn_eq
    -- From n = 15k + 21l, we can derive that n is divisby 3
    have h2 : n % 3 = 0 := by
      rw [h1]
      omega
    -- Since n > 0 and n divisible by 3, so n >= 3
    omega