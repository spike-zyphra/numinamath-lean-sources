import Mathlib

theorem number_theory_4631 : IsLeast {x : ℕ | x > 0 ∧ (7 * x) % 100 = 29} 47 := by
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro x ⟨hx_pos, hx_cong⟩
    by_contra h
    push_neg at h
    interval_cases x <;> omega