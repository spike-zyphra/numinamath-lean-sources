import Mathlib

theorem number_theory_215740 (y : ℝ) (hy : 0 < y) :
    ∃ x, x > y ∧ (x - y) % 71 = 0 ∨ x < y ∧ (y - x) % 71 = 0 := by
  use y + 71
  left
  constructor
  · linarith
  · norm_num
    all_goals ring_nf <;> omega