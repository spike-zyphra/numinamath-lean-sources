import Mathlib

theorem algebra_21266 :
  IsGreatest {u | ∃ (a b c : ℕ), u = a * b * c ∧ a + b + c = 10 + 13 + 14 - 10} 729 := by
  constructor
  · -- Show that 729 is in the set
    use 9, 9, 9
    all_goals norm_num
  · -- Show that 729 is greatest in the set
    intro u hu
    rcases hu with ⟨a, b, c, h1, h2⟩
    have h3 : a * b * c ≤ 729 := by
      have h4 : a + b + c = 27 := by omega
      have h5 : a * b * c ≤ 729 := by
        have h6 : a ≤ 27 := by omega
        have h7 : b ≤ 27 := by omega
        have h8 : c ≤ 27 := by omega
        interval_cases a <;> interval_cases b <;> omega
      nlinarith
    linarith [h1, h3]