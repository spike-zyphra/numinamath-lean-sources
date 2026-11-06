import Mathlib

theorem number_theory_6274 : IsLeast {x | 0 < x ∧ x % 9 = 6 ∧ x % 10 = 7 ∧ x % 11 = 8} 987 := by
  constructor
  · -- Show 987 is positive and satisfies all remainder conditions
    refine' ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
  · -- Show that for any element y in the set, y >= 987
    intro y hy
    rcases hy with ⟨hy_pos, hy_mod9, hy_mod10, hy_mod11⟩
    omega