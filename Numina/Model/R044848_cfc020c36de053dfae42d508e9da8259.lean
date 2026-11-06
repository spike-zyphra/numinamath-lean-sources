import Mathlib

theorem number_theory_286860 :
    IsLeast {x | ∃ n m p, n > 0 ∧ m > 0 ∧ p > 0 ∧ x = 9 * n - 7 ∧ x = 8 * m - 1 ∧ x = 11 * p - 3} 767 := by
  constructor
  · -- Show 767 is indeed in the set
    use 86
    use 96
    use 70
    all_goals norm_num
  · -- Show there is no smaller element in the set
    intro x hx
    rcases hx with ⟨n, m, p, hn, hm, hp, hx1, hx2, hx3⟩
    by_contra h
    push_neg at h
    omega