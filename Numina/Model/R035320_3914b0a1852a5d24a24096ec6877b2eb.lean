import Mathlib

theorem number_theory_285759 :
    Set.ncard {N : ℕ | N > 0 ∧ 2007 % N = 5} = 14 := by
  have h1 : {N : ℕ | N > 0 ∧ 2007 % N = 5} = {7, 11, 13, 14, 22, 26, 77, 91, 143, 154, 182, 286, 1001, 2002} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if $N$ is a solution, then $N$ is in the final set
      intro h
      rcases h with ⟨hN_pos, h1⟩
      have h5 : N > 5 := by 
        by_contra h
        push_neg at h
        interval_cases N <;> norm_num at h1 ⊢ <;> all_goals omega
      have hNle2007 : N ≤ 2007 := by
        by_contra h
        push_neg at h
        have h6 : 2007 % N = 2007 := by
          rw [Nat.mod_eq_of_lt]
          all_goals omega
        have h7 : 2007 % N = 5 := h1
        omega
      interval_cases N <;> norm_num at h1 ⊢
      <;> tauto
    · -- Second direction: if $N$ is in the final set, then it is a solution
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- Case N = 7
        constructor
        · norm_num
        · norm_num
      · -- Case N = 11
        constructor
        · norm_num
        · norm_num
      · -- Case N = 13
        constructor
        · norm_num
        · norm_num
      · -- Case N = 14
        constructor
        · norm_num
        · norm_num
      · -- Case N = 22
        constructor
        · norm_num
        · norm_num
      · -- Case N = 26
        constructor
        · norm_num
        · norm_num
      · -- Case N = 77
        constructor
        · norm_num
        · norm_num
      · -- Case N = 91
        constructor
        · norm_num
        · norm_num
      · -- Case N = 143
        constructor
        · norm_num
        · norm_num
      · -- Case N = 154
        constructor
        · norm_num
        · norm_num
      · -- Case N = 182
        constructor
        · norm_num
        · norm_num
      · -- Case N = 286
        constructor
        · norm_num
        · norm_num
      · -- Case N = 1001
        constructor
        · norm_num
        · norm_num
      · -- Case N = 2002
        constructor
        · norm_num
        · norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }