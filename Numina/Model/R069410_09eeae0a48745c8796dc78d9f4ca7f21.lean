import Mathlib

theorem algebra_13860 : {p : ℕ | Nat.Prime p ∧ 20 < p ∧ p < 30}.encard = 2 := by
  have h1 : {p : ℕ | Nat.Prime p ∧ 20 < p ∧ p < 30} = {23, 29} := by
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume p is a prime between 20 and 30
      intro h
      rcases h with ⟨h_prime, h1, h2⟩
      interval_cases p <;> tauto
    · -- Assume p is in {23, 29}, show it's a prime between 20 and 30
      intro h
      rcases h with (r | r)
      · -- Case p = 23
        rw [r]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- Case p = 29
        rw [r]
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals norm_num