import Mathlib

theorem algebra_15688 : IsGreatest {x | ∃(A M C : ℕ), A + M + C = 12 ∧ x = A * M * C + A * M + M * C + C * A} 112 := by 
  constructor 
  · -- Show that 112 is achievable 
    use 4, 4, 4
    all_goals norm_num
  · -- Show that 112 is the greatest 
    intro x hx
    rcases hx with ⟨A, M, C, h1, h2⟩
    have h3 : A ≤ 12 := by omega
    have h4 : M ≤ 12 := by omega
    have h5 : C ≤ 12 := by omega
    interval_cases A <;> interval_cases M <;> omega