import Mathlib

theorem algebra_14561 : {x : ℤ | x ∣ 20}.ncard = 12 := by
  have h1 : {x : ℤ | x ∣ 20} = {-20, -10, -5, -4, -2, -1, 1, 2, 4, 5, 10, 20} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · intro h
      have h2 : n ≤ 20 := by
        apply Int.le_of_dvd (by norm_num) h
      have h3 : n ≥ -20 := by
        have h4 : -n ∣ 20 := by exact Int.neg_dvd.2 h
        have h5 : -n ≤ 20 := by
          apply Int.le_of_dvd (by norm_num) h4
        linarith
      interval_cases n <;> tauto
    · rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
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
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }