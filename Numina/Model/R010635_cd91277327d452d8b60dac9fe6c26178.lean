import Mathlib

theorem algebra_9074 : {x : ℤ | -2 < x ∧ x ≤ 3} = {-1, 0, 1, 2, 3} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · -- First direction: if -2 < x ∧ x ≤ 3, then x ∈ {-1, 0, 1, 2, 3}
    rintro ⟨h1, h2⟩
    omega
  · -- Second direction: if x ∈ {-1, 0, 1, 2, 3}, then -2 < x ∧ x ≤ 3
    rintro (rfl | rfl | rfl | rfl | rfl)
    · -- Case x = -1
      exact ⟨by norm_num, by norm_num⟩
    · -- Case x = 0
      exact ⟨by norm_num, by norm_num⟩
    · -- Case x = 1
      exact ⟨by norm_num, by norm_num⟩
    · -- Case x = 2
      exact ⟨by norm_num, by norm_num⟩
    · -- Case x = 3
      exact ⟨by norm_num, by norm_num⟩