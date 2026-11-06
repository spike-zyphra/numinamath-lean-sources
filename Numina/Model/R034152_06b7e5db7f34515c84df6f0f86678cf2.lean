import Mathlib

theorem algebra_21781 : {x : ℤ | x ∣ 7}.encard = 4 := by
  have h1 : {x : ℤ | x ∣ 7} = {-7, -1, 1, 7} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n divides 7
      intro h 
      have h2 : n ∣ 7 := h 
      have h3 : n ≤ 7 := by
        apply Int.le_of_dvd (by norm_num) h2
      have h4 : n ≥ -7 := by
        have h5 : -n ∣ 7 := by 
          exact Int.neg_dvd.2 h2
        have h6 : -n ≤ 7 := by 
          apply Int.le_of_dvd (by norm_num) h5
        linarith 
      interval_cases n <;> tauto 
    · -- Assume n in the set
      rintro (rfl | rfl | rfl | rfl)
      · -- n = -7
        norm_num 
      · -- n = -1
        norm_num 
      · -- n = 1
        norm_num 
      · -- n = 7
        norm_num 
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> aesop