import Mathlib

theorem algebra_87362 : IsGreatest {x | ∃ A M C : ℕ, A + M + C = 12 ∧ x = A * M * C + A * M + M * C + C * A} 112 := by
  constructor
  · -- Show that 112 is in the set, so (4, 4, 4)
    use 4, 4, 4
    all_goals norm_num
  · -- Show that for all x in the set, x ≤ 112
    intro x hx
    rcases hx with ⟨A, M, C, hsum, hx⟩
    have h1 : A ≤ 12 := by omega
    have h2 : M ≤ 12 := by omega
    have h3 : C ≤ 12 := by omega
    interval_cases A <;> interval_cases M <;> omega