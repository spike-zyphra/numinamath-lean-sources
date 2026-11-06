import Mathlib

theorem number_theory_183575 :
    IsLeast {n | ∃ a b c : ℕ, a*13+b*29+c*41=1007 ∧ n=a+b+c} 27 := by
  constructor
  · -- Show 27 belongs to the set by finding a solution
    use 1, 6, 20
    all_goals norm_num
  · -- Show that 27 is the least
    intro n hn
    rcases hn with ⟨a, b, c, h1, h2⟩
    by_contra h
    push_neg at h
    have h3 : a + b + c ≤ 26 := by linarith
    omega