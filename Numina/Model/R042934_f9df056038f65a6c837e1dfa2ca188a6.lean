import Mathlib

theorem number_theory_4010 :
    IsLeast {n | ∃ x y : ℤ, 0 < x ∧ 0 < y ∧ 2020 * x - 215 * y = 10000 ∧ n = x + y} 151 := by
  constructor
  · -- Show 151 is in the set
    use 19, 132
    all_goals norm_num
  · -- Show 151 is minimal
    intro n hn
    rcases hn with ⟨x, y, hx, hy, heq, hn⟩
    by_contra h
    push_neg at h
    have h1 : x + y < 151 := by linarith
    omega