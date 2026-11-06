import Mathlib

theorem number_theory_93271 :
    Set.ncard {N : ℕ | N ∈ Finset.Icc 10 99 ∧ ∃ k, N + (10 * (Nat.digits 10 N).headI + (Nat.digits 10 N).tail.headI) = k^2} = 8 := by 
  have h1 : {N : ℕ | N ∈ Finset.Icc 10 99 ∧ ∃ k, N + (10 * (Nat.digits 10 N).headI + (Nat.digits 10 N).tail.headI) = k^2} = {29, 38, 47, 56, 65, 74, 83, 92} := by 
    ext N
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume N is in the set 
      rintro ⟨⟨hN1, hN2⟩, k, hN3⟩ 
      interval_cases N <;> norm_num at hN3 <;> try { 
        all_goals 
        have h4 : k ≤ 19 := by nlinarith 
        interval_cases k <;> norm_num at hN3 <;> tauto 
      }
    · -- Assume N is in the explicit set 
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- N = 29
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 38
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 47
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 56
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 65
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 74
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 83
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
      · -- N = 92
        constructor
        · norm_num 
        · use 11
          all_goals native_decide 
  rw [h1]
  norm_num