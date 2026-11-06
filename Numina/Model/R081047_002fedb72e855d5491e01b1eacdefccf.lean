import Mathlib

theorem number_theory_22898 :
    IsLeast {b | ∃ d1 d2 : ℕ, d1 < b ∧ d2 < b ∧ 47 = d1 * b + d2} 7 := by
  constructor
  · -- Show that 7 belongs to the set
    use 6, 5
    all_goals omega
  · -- Show that 7 is the least element of the set
    intro b
    intro hb
    rcases hb with ⟨d1, d2, h1, h2, h3⟩
    by_contra h
    push_neg at h
    have h4 : b ≤ 6 := by omega
    have h7 : d1 ≤ 5 := by omega
    have h8 : d2 ≤ 5 := by omega
    interval_cases b <;> omega