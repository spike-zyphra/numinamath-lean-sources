import Mathlib

open Real Set
open scoped BigOperators

theorem inequalities_71393 :
  IsGreatest {x | ∃ a b c : ℝ, x = |a| + |b| + |c| ∧
    |a + 2*b - 3*c| ≤ 6 ∧ |a - 2*b + 3*c| ≤ 6 ∧
    |a - 2*b - 3*c| ≤ 6 ∧ |a + 2*b + 3*c| ≤ 6} 6 := by
  constructor
  · -- Show that 6 is achievable with (6, 0, 0)
    use 6, (0 : ℝ), (0 : ℝ)
    norm_num [abs]
  · -- Show that no value greater than 6 is achievable
    rintro x ⟨a, b, c, h_eq, h1, h2, h3, h4⟩
    cases' abs_le.mp h1 with h1_neg h1_pos
    cases' abs_le.mp h2 with h2_neg h2_pos
    cases' abs_le.mp h3 with h3_neg h3_pos
    cases' abs_le.mp h4 with h4_neg h4_pos
    cases' abs_cases a with ha1 ha1
    · cases' abs_cases b with hb1 hb1
      · cases' abs_cases c with hc1 hc1
        · linarith
        · linarith
      · cases' abs_cases c with hc1 hc1
        · linarith
        · linarith
    · cases' abs_cases b with hb1 hb1
      · cases' abs_cases c with hc1 hc1
        · linarith
        · linarith
      · cases' abs_cases c with hc1 hc1
        · linarith
        · linarith
    all_goals
      linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c]
      all_goals
        linarith