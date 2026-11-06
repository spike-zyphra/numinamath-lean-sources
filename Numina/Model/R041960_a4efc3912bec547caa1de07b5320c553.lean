import Mathlib

theorem algebra_18704 :
    Set.ncard {x : ℕ | Odd x ∧ ∃ n, x = n^2 ∧ 5 ≤ x ∧ x ≤ 211} = 6 := by
  have h1 : {x : ℕ | Odd x ∧ ∃ n, x = n^2 ∧ 5 ≤ x ∧ x ≤ 211} = {9, 25, 49, 81, 121, 169} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x in the left side, need to prove x in the right side
      rintro ⟨hx_odd, ⟨n, rfl, h5, h211⟩⟩
      have h2 : n ≤ 14 := by nlinarith
      have h3 : n ≥ 3 := by nlinarith
      have h4 : (n : ℕ) % 2 = 1 := by
        by_contra h
        push_neg at h
        have h5 : (n : ℕ) % 2 = 0 := by omega
        have h6 : (n ^ 2) % 2 = 0 := by
          have h7 : n % 2 = 0 := h5
          simp [Nat.pow_mod, h7]
        have h7 : (n ^ 2) % 2 = 1 := by
          have h9 : Odd (n ^ 2) := by
            simpa using hx_odd
          rcases h9 with ⟨k, hk⟩
          omega
        omega
      interval_cases n <;> norm_num at *
      <;> tauto
    · -- Assume x in the right side, need to prove x in the left side
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Show 9 is in the left side
        constructor
        · -- Show 9 is odd
          decide
        · -- Show ∃n, 9 = n^2 ∧ 5 ≤ 9 ∧ 9 ≤ 211
          use 3
          all_goals norm_num
      · -- Show 25 is in the left side
        constructor
        · -- Show 25 is odd
          decide
        · -- Show ∃n, 25 = n^2 ∧ 5 ≤ 25 ∧ 25 ≤ 211
          use 5
          all_goals norm_num
      · -- Show 49 is in the left side
        constructor
        · -- Show 49 is odd
          decide
        · -- Show ∃n, 49 = n^2 ∧ 5 ≤ 49 ∧ 49 ≤ 211
          use 7
          all_goals norm_num
      · -- Show 81 is in the left side
        constructor
        · -- Show 81 is odd
          decide
        · -- Show ∃n, 81 = n^2 ∧ 5 ≤ 81 ∧ 81 ≤ 211
          use 9
          all_goals norm_num
      · -- Show 121 is in the left side
        constructor
        · -- Show 121 is odd
          decide
        · -- Show ∃n, 121 = n^2 ∧ 5 ≤ 121 ∧ 121 ≤ 211
          use 11
          all_goals norm_num
      · -- Show 169 is in the left side
        constructor
        · -- Show 169 is odd
          decide
        · -- Show ∃n, 169 = n^2 ∧ 5 ≤ 169 ∧ 169 ≤ 211
          use 13
          all_goals norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]