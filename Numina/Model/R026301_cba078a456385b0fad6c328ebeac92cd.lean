import Mathlib

theorem algebra_19504 : IsLeast {x | ∃ A B C : ℤ, A ≠ B ∧ A ≠ C ∧ B ≠ C ∧ A * (B - C) = x ∧ 4 ∈ [A, B, C] ∧ 5 ∈ [A, B, C] ∧ 6 ∈ [A, B, C]} (-10) := by
  constructor
  · -- Show -10 is in the set
    use 5, 4, 6
    all_goals norm_num
  · -- Show -10 is minimal in the set
    intro x hx 
    rcases hx with ⟨A, B, C, h1, h2, h3, heq, h4, h5, h6⟩
    norm_num at h4 h5 h6
    have h7 : A = 4 ∨ B = 4 ∨ C = 4 := by 
      tauto
    have h8 : A = 5 ∨ B = 5 ∨ C = 5 := by 
      tauto
    have h9 : A = 6 ∨ B = 6 ∨ C = 6 := by 
      tauto
    have h10 : A ≤ 6 := by
      omega
    have h11 : B ≤ 6 := by
      omega
    have h12 : C ≤ 6 := by 
      omega
    have h13 : A ≥ 4 := by
      omega
    have h14 : B ≥ 4 := by
      omega
    have h15 : C ≥ 4 := by
      omega
    interval_cases A <;> interval_cases B <;> interval_cases C 
      <;> omega