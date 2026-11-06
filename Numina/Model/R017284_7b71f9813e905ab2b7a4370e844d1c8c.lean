import Mathlib

theorem number_theory_123241 :
    IsLeast {n : ℕ | ∃ a b : ℕ, a > 0 ∧ b > 0 ∧ 11 ∣ a + 13 * b ∧ 13 ∣ a + 11 * b ∧ n = a + b} 28 := by
  constructor
  · -- Show 28 in the set
    use 23, 5
    all_goals norm_num
  · -- Show that 28 is the least
    intro n hn
    rcases hn with ⟨a, b, ha, hb, h11, h13, hn⟩
    by_contra h
    push_neg at h
    have h_eq : a + b < 28 := by
      omega
    have h2 : a ≤ 26 := by
      omega
    have h3 : b ≤ 26 := by
      omega
    interval_cases a <;> interval_cases b
    <;> omega