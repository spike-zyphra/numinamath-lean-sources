import Mathlib

theorem number_theory_5618 : {x | x > 0 ∧ 1216 % x = 0}.encard = 14 := by
  have h1 : {x | x > 0 ∧ 1216 % x = 0} = {1, 2, 4, 8, 16, 32, 64, 19, 38, 76, 152, 304, 608, 1216} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Suppose x is a positive divisor of 1216
      intro h
      rcases h with ⟨hx_pos, hx_div⟩
      have h2 : x ≤ 1216 := by
        by_contra h3
        push_neg at h3
        have h4 : 1216 % x = 1216 := by
          rw [Nat.mod_eq_of_lt]
          linarith
          all_goals omega
        omega
      interval_cases x <;> tauto
    · -- Show that these numbers indeed divide 1216
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      all_goals
        constructor <;> norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try native_decide