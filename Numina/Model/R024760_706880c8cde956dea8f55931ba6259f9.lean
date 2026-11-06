import Mathlib

theorem number_theory_282388 (A : Set ℚ) (hA : A = {z : ℚ | ∃ p q : ℕ, p > 0 ∧ q > 0 ∧ p + q = 5 ∧ z = p / q}) :
    A = {1 / 4, 3 / 2, 2 / 3, 4} := by 
  ext z 
  simp only [hA, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume z ∈ A, we need to show z ∈ {1/4, 3/2, 2/3, 4}
    rintro ⟨p, q, hp, hq, hsum, heq⟩
    have h1 : p ≤ 4 := by omega
    have h2 : q ≤ 4 := by omega
    interval_cases p <;> interval_cases q
    <;> norm_num [heq] at *
    <;> tauto
  · -- Assume z ∈ {1/4, 3/2, 2/3, 4}, we need to show z ∈ A
    rintro (rfl | rfl | rfl | rfl)
    · -- z = 1/4
      use 1, 4
      all_goals norm_num
    · -- z = 3/2
      use 3, 2
      all_goals norm_num
    · -- z = 2/3
      use 2, 3
      all_goals norm_num
    · -- z = 4
      use 4, 1
      all_goals norm_num