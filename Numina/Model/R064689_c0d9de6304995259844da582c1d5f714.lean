import Mathlib

theorem number_theory_1382 : {p | p.Prime ∧ p < 100 ∧ p ∣ 3^32 - 2^32} = {5, 13, 17, 97} := by
  ext p
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, 
    Set.union_singleton]
  constructor
  · -- Assume p is a prime less than 100 that divides 3^32 - 2^32, show p ∈ {5, 13, 17, 97}
    intro h
    rcases h with ⟨h_prime, h_lt, h_div⟩
    interval_cases p <;> norm_num at *
    <;> try { contradiction }
    <;> try { tauto }
  
  · -- Assume p ∈ {5, 13, 17, 97}, show p is prime and less than 100 and divides 3^32 - 2^32
    rintro (rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num
    · constructor
      · norm_num
      constructor
      · norm_num
      · norm_num