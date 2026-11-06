import Mathlib

theorem algebra_205768 :
    IsLeast {z : ℕ | ∃ x y, z = 7 * x + 5 * y ∧ 5 ∣ x + 2 * y ∧ 3 ∣ x + y ∧ 99 ≤ 2 * x + y} 366 := by
  constructor
  · -- Show 366 is in the set
    use 48, 6
    all_goals norm_num 
  · -- Show 366 is minimal 
    intro z h
    rcases h with ⟨x, y, h_eq, h1, h2, h3⟩
    by_contra h4
    push_neg at h4 
    have h4 : 7 * x + 5 * y < 366 := by 
      omega 
    have h6 : x ≤ 52 := by 
      omega 
    have h7 : y ≤ 53 := by 
      omega 
    interval_cases x <;> omega