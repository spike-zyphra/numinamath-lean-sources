import Mathlib

theorem algebra_205988 :
    IsGreatest {n | ∃ x y : ℕ, 69 * x + 54 * y ≤ 2008 ∧ n = x * y} 270 := by 
  constructor
  · -- Show 270 is achievable
    use 15, 18
    all_goals norm_num
  · -- Show there is no greater
    intro n hn
    rcases hn with ⟨x, y, h1, rfl⟩
    by_contra h
    push_neg at h
    have h1' : x ≤ 29 := by 
      nlinarith
    have h2' : y ≤ 37 := by 
      nlinarith
    interval_cases x <;> interval_cases y <;> omega