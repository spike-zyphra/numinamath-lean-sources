import Mathlib

theorem number_theory_176833 : {n : ℕ | n < 50 ∧ Odd (Nat.divisors n).card}.encard = 7 := by 
  have h1 : {n : ℕ | n < 50 ∧ Odd (Nat.divisors n).card} = {1, 4, 9, 16, 25, 36, 49} := by
    ext n 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor 
    · -- If n has less than 50 and has an odd number of divisors
      intro hn 
      rcases hn with ⟨h1, h2⟩ 
      interval_cases n <;> try tauto
      <;> try decide
    · -- If n ∈ {1,4,9,16,25,36,49}, then n < 50 and has an odd number of divisors
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
  rw [Set.encard]
  simp [Set.ncard]
  <;> try native_decide