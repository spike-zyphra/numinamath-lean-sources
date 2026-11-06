import Mathlib

theorem number_theory_202430 :
    {N : ℕ | 2017 % N = 17}.encard = 13 := by
  have h1 : {N : ℕ | 2017 % N = 17} = {20, 25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000} := by
    ext N
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
      Set.union_singleton]
    constructor
    · -- If 2017 % N = 17, then N ∈ {20, 25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000}
      intro h
      have h2 : N ≤ 2017 := by
        by_contra h2
        push_neg at h2
        have h3 : 2017 % N = 2017 := by
          rw [Nat.mod_eq_of_lt]
          all_goals omega
        omega
      interval_cases N <;> norm_num at h ⊢ <;> tauto
    · -- If N ∈ {20, 25, 40, 50, 80, 100, 125, 200, 250, 400, 500, 1000, 2000}, then 2017 % N = 17
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard]
  <;> try { rfl }
  <;> try { omega }