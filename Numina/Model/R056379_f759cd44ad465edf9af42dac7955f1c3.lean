import Mathlib

theorem number_theory_19117 :
    IsGreatest {p | ∃ x y, p = x * y ∧ x.Prime ∧ y.Prime ∧ x < 40 ∧ y < 40 ∧ x ≠ y} 1147 := by
  constructor
  · -- Show that 1147 is in the set
    use 31, 37
    all_goals norm_num
    <;> try { norm_num }
  · -- We need to show that if p is in the set, then p ≤ 1147
    intro p hp
    rcases hp with ⟨x, y, h_eq, hx, hy, hx40, hy40, hne⟩
    interval_cases x <;> interval_cases y
    <;> norm_num [h_eq] at *
    <;> try { tauto }
    <;> try { contradiction }