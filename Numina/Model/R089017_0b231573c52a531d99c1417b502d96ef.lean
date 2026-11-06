import Mathlib

theorem number_theory_266937 : {n | 1 < n ∧ n ≤ 88 ∧ 6 ∣ n} =
    {6, 12, 18, 24, 30, 36, 42, 48, 54, 60, 66, 72, 78, 84} := by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Prove the forward direction: if n is in the left set, then n is in the right set.
    rintro ⟨h1, h2, h3⟩
    interval_cases n <;> tauto
  · -- Prove the backward direction: if n is in the right set, then n is in the left set.
    rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    all_goals
      constructor <;> decide