import Mathlib

theorem number_theory_22933 :
    Set.ncard {x | x ∣ 1000 ∧ 20 ∣ x} = 6 := by

  have h1 : {x | x ∣ 1000 ∧ 20 ∣ x} = {20, 40, 100, 200, 500, 1000} := by 
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff,
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume n is a divisor of 1000 and 20 divides n
      rintro ⟨h1, h2⟩
      have h3 : n ≤ 1000 := by 
        exact Nat.le_of_dvd (by norm_num) h1
      interval_cases n <;> norm_num at h1 h2 <;> tauto
    · -- Show that these numbers indeed divide 1000 and are multiples of 20
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
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
  all_goals norm_num