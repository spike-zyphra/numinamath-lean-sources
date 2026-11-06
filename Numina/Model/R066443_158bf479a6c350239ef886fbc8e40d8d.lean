import Mathlib

theorem number_theory_4764 (x y : ℤ) (hx : 0 < x) (hy : 0 < y)
    (h : 5 * x - 6 * y = 1) :
    IsLeast {x | ∃ y : ℤ, 0 < x ∧ 0 < y ∧ 5 * x - 6 * y = 1} 5 := by
  constructor
  · -- Show 5 is in the set
    use 4
    all_goals norm_num
  · -- Show 5 is the minimum: if x is in the set, then x ≥ 5
    intro x hx
    rcases hx with ⟨y, hx, hy, heq⟩
    by_contra h2
    push_neg at h2
    have h3 : x < 5 := by linarith
    have h4 : x ≥ 1 := by linarith
    interval_cases x <;> omega