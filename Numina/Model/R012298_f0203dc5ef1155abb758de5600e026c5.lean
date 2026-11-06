import Mathlib

theorem number_theory_609359:
  IsGreatest {k : ℕ | ∃ a b c d e : ℕ, 625 * a + 250 * b + 100 * c + 40 * d + 16 * e = 15 ^ 3 ∧
   a + b + c + d + e = k} 153 := by
  constructor
  · -- Show that 153 is in the set
    use 1, 1, 1, 0, 150
    all_goals norm_num
  · -- Show that 153 is greatest
    intro k hk
    rcases hk with ⟨a, b, c, d, e, h₁, h₂⟩
    by_contra h
    push_neg at h
    have h3 : a + b + c + d + e > 153 := by omega
    omega