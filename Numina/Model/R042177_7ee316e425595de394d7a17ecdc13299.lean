import Mathlib

theorem number_theory_177583 :
    Set.ncard {x : ℕ | 0 < x ∧ (2014 % (x + 1)) = 0} = 7 := by
  have h1 : {x : ℕ | 0 < x ∧ (2014 % (x + 1)) = 0} = {1, 18, 37, 52, 105, 1006, 2013} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume x is in {x | 0 < x ∧ (2014 % (x + 1)) = 0}
      intro h
      rcases h with ⟨hx1, hx2⟩
      have h2 : x ≤ 2013 := by
        by_contra h
        push_neg at h
        have h3 : x + 1 > 2014 := by linarith
        have h4 : 2014 % (x + 1) = 2014 := by
          rw [Nat.mod_eq_of_lt]
          all_goals
            linarith
        rw [h4] at hx2
        all_goals omega
      interval_cases x <;> tauto
    · -- Assume x is in {1, 18, 37, 52, 105, 1006, 2013}
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  all_goals try native_decide