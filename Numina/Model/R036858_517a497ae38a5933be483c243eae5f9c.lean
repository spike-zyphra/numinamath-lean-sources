import Mathlib

theorem number_theory_304273 (m n : ℤ) (hm : 0 < m) (hn : 0 < n)
    (h : 2000 / 2001 < n / m ∧ n / m < 2001 / 2002) :
    IsLeast {x | ∃ m n : ℤ, 0 < m ∧ 0 < n ∧ 2000 / 2001 < n / m ∧ n / m < 2001 / 2002 ∧ x = n / m} (4001 / 4003) := by
  norm_num at h ⊢
  all_goals
    omega