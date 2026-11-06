import Mathlib

theorem number_theory_609302:
{x: ℕ | 10 ≤ x ∧ x ≤ 99 ∧ Nat.Prime x ∧ Nat.Prime (x % 10) ∧ Nat.Prime (x / 10)}.encard = 4 := by
  have h1 : {x : ℕ | 10 ≤ x ∧ x ≤ 99 ∧ Nat.Prime x ∧ Nat.Prime (x % 10) ∧ Nat.Prime (x / 10)} = {23, 37, 53, 73} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x satisfies the conditions
      intro h
      rcases h with ⟨h10, h99, hprime, hprimes, hprimes2⟩
      interval_cases x <;> norm_num at *
      <;> tauto
    · -- Assume x ∈ {23, 37, 53, 73}
      rintro (rfl | rfl | rfl | rfl)
      all_goals
        constructor
        · norm_num
        all_goals constructor
        · norm_num
        all_goals constructor
        · norm_num [Nat.Prime]
        all_goals constructor
        · norm_num [Nat.Prime]
        · norm_num [Nat.Prime]
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> rfl