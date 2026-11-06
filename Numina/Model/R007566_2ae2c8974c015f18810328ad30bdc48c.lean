import Mathlib

theorem algebra_20889 : { p : ℝ | 0 ≥ 54 * p - 144 ∧ 0 > 12 - 20 * p } = Set.Ioc (3 / 5) (8 / 3) := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_Ioc]
  constructor
  · -- Assume p satisfies both inequalities
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that 3/5 < p from the second inequality
      linarith
    · -- Show that p ≤ 8/3 from the first inequality
      linarith
  · -- Assume p is in the interval (3/5, 8/3]
    rintro ⟨h1, h2⟩
    constructor
    · -- Show that 0 ≥ 54p - 144 from p ≤ 8/3
      linarith
    · -- Show that 0 > 12 - 20p from 3/5 < p
      linarith