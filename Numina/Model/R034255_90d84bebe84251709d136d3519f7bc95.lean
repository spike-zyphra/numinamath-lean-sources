import Mathlib

theorem number_theory_275860 :
    Set.ncard {x : ℕ | x ∣ 2020 ∧ x.divisors.card > 3} = 7 := by 
  have h1 : {x : ℕ | x ∣ 2020 ∧ x.divisors.card > 3} = 
      {10, 20, 202, 404, 505, 1010, 2020} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- If n divides 2020 and has more than 3 divisors, then n is in the right side set.
      intro h
      rcases h with ⟨hdiv, hdivcount⟩
      have h2 : n ≤ 2020 := by
        exact Nat.le_of_dvd (by norm_num) hdiv
      interval_cases n <;> norm_num at hdiv hdivcount ⊢
      <;> try { tauto }
    · -- If n is in the right side set, then it divides 2020 and has more than 3 divisors.
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · constructor
        · norm_num
        · native_decide
      · constructor
        · norm_num
        · native_decide
      · constructor
        · norm_num
        · native_decide
      · constructor
        · norm_num
        · native_decide
      · constructor
        · norm_num
        · native_decide
      · constructor
        · norm_num
        · native_decide
      · constructor
        · norm_num
        · native_decide
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }