import Mathlib


theorem number_theory_165021 :
    IsGreatest {x | ∃ a b c d e : ℕ, x = a + b + c + d + e ∧ 625 * a + 250 * b + 100 * c + 40 * d + 16 * e = 15 ^ 3} 153 := by
  constructor
  · -- Show 153 is achievable
    use 1, 1, 1, 0, 150
    all_goals
      norm_num
  · -- Show that 153 is the greatest
    intro x hx
    rcases hx with ⟨a, b, c, d, e, h_eq, heq⟩
    omega