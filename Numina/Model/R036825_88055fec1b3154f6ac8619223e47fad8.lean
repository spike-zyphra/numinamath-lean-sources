import Mathlib

theorem number_theory_97697 : {d : ℤ | ∃ a b, (0 < a) ∧ (0 < b) ∧ (a ≤ 9) ∧ (b ≤ 9) ∧ (d = 10 * a + b - (10 * b + a))} ∩ {45, 46, 47, 48, 49} = {45} := by
  ext x 
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume that x is in the set of differences and in the given set
    rintro ⟨⟨a, b, ha1, hb1, ha2, hb2, hx⟩, h⟩
    rcases h with (rfl | rfl | rfl | rfl | rfl)
    · 
      simp at *
    · 
      omega
    · 
      omega
    · 
      omega
    · 
      omega
  · -- Assume x is in {45}
    intro hx
    rw [hx]
    constructor
    · -- Show there exists a and b for x = 45
      use 6, 1
      all_goals
        norm_num
    · 
      norm_num