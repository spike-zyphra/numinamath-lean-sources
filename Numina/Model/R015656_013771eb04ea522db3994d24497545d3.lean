import Mathlib

theorem number_theory_94015 :
    Set.ncard {x : ℕ | x ∣ 2020 ∧ x ≠ 0 ∧ x.divisors.card > 3} = 7 := by
  have h1 : {x : ℕ | x ∣ 2020 ∧ x ≠ 0 ∧ x.divisors.card > 3} = {10, 20, 202, 404, 505, 1010, 2020} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume n is in the set
      intro h
      rcases h with ⟨h1, hn1, h2⟩
      have h3 : n ≤ 2020 := by 
        exact Nat.le_of_dvd (by norm_num) h1
      have h4 : n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 5 ∨ n = 10 ∨ n = 20 ∨ n = 101 ∨ n = 202 ∨ n = 404 ∨ n = 505 ∨ n = 1010 ∨ n = 2020 := by
        interval_cases n <;> norm_num at h1 ⊢ 
      rcases h4 with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 1
        exfalso
        have h : (1 : Nat).divisors.card = 1 := by
          native_decide
        omega
      · -- n = 2
        exfalso
        have h : (2 : Nat).divisors.card = 2 := by
          native_decide
        omega
      · -- n = 4
        exfalso
        have h : (4 : Nat).divisors.card = 3 := by
          native_decide
        omega
      · -- n = 5
        exfalso
        have h : (5 : Nat).divisors.card = 2 := by
          native_decide
        omega
      · -- n = 10
        simp
      · -- n = 20
        simp
      · -- n = 101
        exfalso
        have h : (101 : Nat).divisors.card = 2 := by
          native_decide
        omega
      · -- n = 202
        simp
      · -- n = 404
        simp
      · -- n = 505
        simp
      · -- n = 1010
        simp
      · -- n = 2020
        simp
    · -- Show that if n is in {10, 20, 202, 404, 505, 1010, 2020}, then n is in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- n = 10
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
      · -- n = 20
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
      · -- n = 202
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
      · -- n = 404
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
      · -- n = 505
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
      · -- n = 1010
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
      · -- n = 2020
        constructor
        · exact by norm_num
        constructor
        · norm_num
        · native_decide
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide