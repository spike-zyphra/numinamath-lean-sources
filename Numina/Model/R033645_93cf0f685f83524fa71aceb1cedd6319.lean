import Mathlib

def is_seven_star_number (N : ℕ) : Prop :=
  {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0}.ncard ≥ 7

theorem number_theory_106003 :
    IsLeast {N | 2000 < N ∧ is_seven_star_number N} 2016 := by
  constructor
  · -- Show 2016 is in the set
    constructor
    · norm_num
    · -- Show 2016 is a seven star number
      unfold is_seven_star_number
      have h1 : {k | k ∈ Finset.Icc 1 9 ∧ (2016 : ℕ) % k = 0} = {1, 2, 3, 4, 6, 7, 8, 9} := by
        ext k
        simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · -- Assume k ∈ { k | k ∈ [1, 9] ∧ 2016 % k = 0 }
          rintro ⟨⟨hk1, hk2⟩, hdiv⟩
          interval_cases k <;> tauto
        · -- Assume k ∈ {1, 2, 3, 4, 6, 7, 8, 9}
          rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · -- k = 1
            constructor <;> norm_num
          · -- k = 2
            constructor <;> norm_num
          · -- k = 3
            constructor <;> norm_num
          · -- k = 4
            constructor <;> norm_num
          · -- k = 6
            constructor <;> norm_num
          · -- k = 7
            constructor <;> norm_num
          · -- k = 8
            constructor <;> norm_num
          · -- k = 9
            constructor <;> norm_num
      rw [h1]
      rw [Set.ncard_eq_toFinset_card']
      simp [Finset.card_insert_of_not_mem, Finset.card_singleton]
      <;> try { native_decide }
  · -- Show 2016 is minimal
    intro N hN
    rcases hN with ⟨hN1, hN2⟩
    unfold is_seven_star_number at hN2
    by_contra h
    push_neg at h
    have hN3 : N < 2016 := by nlinarith
    have hN4 : {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0}.ncard ≥ 7 := by
      simpa using hN2
    have hN4' : {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0} = Finset.filter (fun k => N % k = 0) (Finset.Icc 1 9) := by
      ext k
      simp
    rw [hN4'] at hN4
    rw [Set.ncard_coe_Finset] at hN4
    interval_cases N <;> try { contradiction }
    <;> try { native_decide }