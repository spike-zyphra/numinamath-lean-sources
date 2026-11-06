import Mathlib

theorem number_theory_199007 :
    ∑ᶠ P ∈ {P | Nat.Prime P ∧ Nat.Prime (P + 2) ∧ P * (P + 2) ≤ 2007}, P = 106 := by
  have h1 : {P | Nat.Prime P ∧ Nat.Prime (P + 2) ∧ P * (P + 2) ≤ 2007} = {3, 5, 11, 17, 29, 41} := by
    ext P
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward direction: if P is in the set, then it's one of these primes
      intro h
      rcases h with ⟨h_prime, h_prime2, h_le⟩
      have h2 : P ≤ 44 := by nlinarith
      interval_cases P <;> norm_num at *
      <;> try { contradiction }
      <;> norm_num at h_prime h_prime2 h_le <;> tauto
    · -- Reverse direction: if P is one of these primes, then it's in the set
      rintro (rfl | rfl | rfl | rfl | rfl | rfl)
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
  rw [h1]
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]
  <;> try native_decide
  <;> try { contradiction }