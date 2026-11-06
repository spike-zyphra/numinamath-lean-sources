import Mathlib

theorem algebra_14754 :
    Set.ncard {x : ℕ | x > 0 ∧ 40 % x = 0 ∧ 72 % x = 0} = 4 := by
  have h1 : {x : ℕ | x > 0 ∧ 40 % x = 0 ∧ 72 % x = 0} = {1, 2, 4, 8} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, 
      Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume x is in the set
      intro h
      rcases h with ⟨hx1, hx2, hx3⟩
      have h2 : x ∣ 40 := by
        exact Nat.dvd_of_mod_eq_zero hx2
      have h3 : x ∣ 72 := by
        exact Nat.dvd_of_mod_eq_zero hx3
      have h4 : x ∣ Nat.gcd 40 72 := by
        exact Nat.dvd_gcd h2 h3
      have h5 : Nat.gcd 40 72 = 8 := by
        norm_num [Nat.gcd]
      rw [h5] at h4
      have h6 : x ≤ 8 := by 
        exact Nat.le_of_dvd (by norm_num) h4
      interval_cases x <;> norm_num at *
    · -- Assume x is in {1, 2, 4, 8}
      rintro (rfl | rfl | rfl | rfl)
      · -- x = 1
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- x = 2
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- x = 4
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
      · -- x = 8
        constructor
        · norm_num
        constructor
        · norm_num
        · norm_num
  rw [h1]
  norm_num [Set.ncard_insert_of_not_mem, Set.ncard_singleton]