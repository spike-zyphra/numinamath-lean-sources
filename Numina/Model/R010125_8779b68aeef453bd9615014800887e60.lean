import Mathlib

theorem number_theory_216275 :
    IsLeast {n : ℕ | ∃ a b c d : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
      a^2 + b^2 = n ∧ c^2 + d^2 = n} 65 := by
  constructor
  · -- Show that 65 is indeed in the set.
    use 1, 8, 4, 7
    all_goals norm_num

  · -- Show that 65 is the smallest element in the set.
    intro n hn
    rcases hn with ⟨a, b, c, d, ha, hb, hc, hd, hab, hac, had, hbc, hbd, hcd, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : a ≤ 8 := by nlinarith
    have h4 : b ≤ 8 := by nlinarith
    have h5 : c ≤ 8 := by nlinarith
    have h6 : d ≤ 8 := by nlinarith

    interval_cases a <;> interval_cases b <;> interval_cases c <;> interval_cases d
    <;> omega