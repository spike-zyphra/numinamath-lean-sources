import Mathlib

theorem number_theory_283102 (a b c : ℕ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hdiff : a ≠ b ∧ a ≠ c ∧ b ≠ c) (hprod : a * b * c = 72) :
    IsLeast {x | ∃ a b c : ℕ, 0 < a ∧ 0 < b ∧ 0 < c ∧ a ≠ b ∧ a ≠ c ∧ b ≠ c ∧ a * b * c = 72 ∧ x = a + b + c} 13 := by

  constructor
  · -- We will show 13 is achievable via the triplet (3, 4, 6).
    use 3, 4, 6
    all_goals
      norm_num

  · -- We will prove there is no smaller element in the set.
    intro x hx
    rcases hx with ⟨a, b, c, ha, hb, hc, h1, h2, h3, hprod, hx⟩
    by_contra h
    push_neg at h

    have h : a + b + c < 13 := by linarith
    have h4 : a < 13 := by nlinarith
    have h5 : b < 13 := by nlinarith
    have h6 : c < 13 := by nlinarith

    interval_cases a <;> interval_cases b <;> interval_cases c <;> omega