import Mathlib

theorem inequalities_9522 : {x : ℕ | 0 < x ∧ x^2 < 264 - 10 * x}.encard = 11 := by
  have h1 : {x : ℕ | 0 < x ∧ x^2 < 264 - 10 * x} = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- First, we show that if $n$ is in the set, then $n \in \{1,2, \cdots, 11\}$.
      intro h
      rcases h with ⟨h2, h3⟩
      have h4 : n <= 11 := by
        by_contra h
        push_neg at h
        have h5 : n >= 12 := by omega
        have h6 : n ^ 2 >= 144 := by nlinarith
        have h7 : 10 * n >= 120 := by nlinarith
        have h8 : n ^ 2 + 10 * n >= 264 := by nlinarith
        have h9 : n ^ 2 <= 264 - 10 * n := by
          omega
        have h10 : n ^ 2 + 10 * n < 264 := by
          omega
        omega
      interval_cases n <;> tauto
    · -- Now the reverse: if $n \in \{1,2, \cdots, 11\}$, then $n$ is in the set.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
      · constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> try { try { tauto } }
  all_goals omega