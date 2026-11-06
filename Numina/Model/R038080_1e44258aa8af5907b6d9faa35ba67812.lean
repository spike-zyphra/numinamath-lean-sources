import Mathlib

theorem algebra_6325 : IsGreatest {x | |x| ≤ 2440 ∧ ∃ k : ℤ, (x ^ 2 + 2020) / (x + 20) = k} 2440 := by
  constructor
  · -- Show that 2440 is in the set
    constructor
    · -- Show |2440| ≤ 2440
      norm_num
    · -- Show that ∃ k : ℤ, (2440 ^ 2 + 2020) / (2440 + 20) = k
      use (2440 ^ 2 + 2020) / (2440 + 20)
      all_goals norm_num
  · -- Show that if x in the set then x ≤ 2440
    intro x hx
    rcases hx with ⟨hx1, ⟨k, hk⟩⟩
    have h1 : |x| ≤ 2440 := hx1
    cases' abs_le.mp h1 with h3 h4
    linarith