import Mathlib

theorem algebra_93492 : IsGreatest {n : ℕ | ∃ A M C : ℕ, A + M + C = 10 ∧ n = A * M * C + A * M + M * C + C * A} 69 := by
  constructor
  · -- Show that 69 is in the set
    use 3, 3, 4
    all_goals
      norm_num
  · -- Show that any element in the set is ≤ 69
    intro n hn
    rcases hn with ⟨A, M, C, h1, h2⟩
    have h3 : A ≤ 10 := by omega
    have h4 : M ≤ 10 := by omega
    have h5 : C ≤ 10 := by omega
    interval_cases A <;> interval_cases M <;> omega