import Mathlib

theorem number_theory_4887 : IsLeast {x : ℕ | 0 < x ∧ (4^(2023 - x) % 61 = 3)} 10 := by
  constructor
  · -- Show 10 belongs to the set.
    constructor
    · norm_num
    · norm_num
  · -- Show there is no smaller element in the set
    intro y hy
    rcases hy with ⟨hy_pos, hy_cong⟩
    by_contra h
    push_neg at h
    interval_cases y <;> norm_num at hy_cong <;> omega