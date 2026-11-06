import Mathlib

theorem number_theory_7083 : IsLeast {x | ∃ a b c : ℕ, x = a + b + c ∧ 31^a + 2^b = c^2} 6 := by
  constructor
  · -- Show 6 is in the set
    use 0, 3, 3
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨a, b, c, h_eq, heq⟩
    by_contra h
    push_neg at h
    have h1 : a + b + c < 6 := by linarith
    have h2 : a ≤ 5 := by
      omega
    have h3 : b ≤ 5 := by
      omega
    have h4 : c ≤ 5 := by
      omega
    interval_cases a <;> interval_cases b <;> interval_cases c
    <;> omega