import Mathlib

theorem number_theory_6802 :
    IsLeast {x : ℕ | 25 < x ∧ x^2 % 11 = 4} 31 := by
  constructor 
  · -- Show that 31 belongs to the set
    constructor
    · norm_num
    · norm_num
  · -- Show that 31 is minimal, if $x$ is in the set, then $31 \le x$
    intro x hx
    rcases hx with ⟨hx1, hx2⟩
    by_contra h
    push_neg at h
    interval_cases x <;> norm_num at hx1 hx2 <;> all_goals omega