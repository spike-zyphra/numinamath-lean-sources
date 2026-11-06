import Mathlib

theorem algebra_4952 :
    IsLeast {k : ℕ | ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ 7 * x + 9 * y = 228 ∧ k = x * y} 60 := by
  constructor
  · -- First, prove that 60 is indeed achievable, using x = 30 and y = 2.
    use 30, 2
    all_goals norm_num
  · -- Now, prove that 60 is the least element in the set.
    intro k hk
    rcases hk with ⟨x, y, hx_pos, hy_pos, h_eq, hk⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ 32 := by
      nlinarith
    have h2 : y ≤ 25 := by
      nlinarith
    interval_cases x <;> interval_cases y
    <;> omega