import Mathlib

def is_ap (a d : ℤ) := a > 0 ∧ d > 0 ∧ a + d > 0 ∧ a + 2 * d > 0

def is_right_triangle (a d : ℤ) := a ^ 2 + (a + d) ^ 2 = (a + 2 * d) ^ 2

theorem number_theory_158 :
    {81} ∩ {a : ℤ | ∃ d : ℤ, is_ap a d ∧ is_right_triangle a d} = {81} := by
  ext x
  simp only [Set.mem_inter, Set.mem_singleton_iff, Set.mem_setOf_eq]
  constructor
  · -- Assume x ∈ {81} ∩ {a : ℤ | ∃ d : ℤ, is_ap a d ∧ is_right_triangle a d}
    rintro ⟨hx, ⟨d, ⟨ha1, hd1, ha2, ha3⟩, h⟩⟩
    exact hx
  · -- Assume x = 81 and show x ∈ {81} ∩ {a : ℤ | ∃ d : ℤ, is_ap a d ∧ is_right_triangle a d}
    intro hx1
    rw [hx1]
    constructor
    · -- Show 81 ∈ {81}
      simp
    · -- Show that ∃d : ℤ, is_ap 81 d ∧ is_right_triangle 81 d
      use 27
      constructor
      · -- Show sides are in AP.
        simp [is_ap]
        all_goals norm_num
      · -- Show right triangle condition
        norm_num [is_right_triangle]