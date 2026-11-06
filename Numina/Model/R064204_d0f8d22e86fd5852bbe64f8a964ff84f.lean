import Mathlib

theorem number_theory_4000 :
  IsLeast {n : ℕ | ∃ x y : ℕ, n = x ^ 2 + y ^ 2 ∧ 13 * x - 73 * y = 163} 1241 := by
  constructor
  · -- Show 1241 is achievable
    use 35, 4
    all_goals norm_num
  · -- Show no smaller element is in the set
    intro n hn
    rcases hn with ⟨x, y, h_eq, heq⟩
    by_contra h
    push_neg at h
    have h1 : x ≤ 35 := by
      nlinarith [show x ^ 2 + y ^ 2 < 1241 by linarith]
    have h2 : y ≤ 35 := by
      nlinarith [show x ^ 2 + y ^ 2 < 1241 by linarith]
    interval_cases x <;> interval_cases y
    <;> omega