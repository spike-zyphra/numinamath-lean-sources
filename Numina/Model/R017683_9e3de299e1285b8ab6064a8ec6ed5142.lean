import Mathlib

def is_Immortals (N : ℕ) : Prop :=
  {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0}.ncard ≥ 8

theorem number_theory_235620 :
    IsLeast {N | 2000 < N ∧ is_Immortals N} 2016 := by
  constructor
  · -- Show 2016 is in the set
    constructor
    · -- Show 2016 > 2000
      norm_num
    · -- Show 2016 is an Immortals
      unfold is_Immortals
      have h1 : {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0} = {1, 2, 3, 4, 6, 7, 8, 9} := by
        ext k
        simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
        constructor
        · -- Assume k in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
          rintro ⟨⟨hk1, hk2⟩, hdiv⟩
          interval_cases k <;> norm_num at *
        · -- Assume k in {1, 2, 3, 4, 6, 7, 8, 9}
          rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
          · -- Show 1 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 2 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 3 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 4 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 6 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 7 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 8 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
          · -- Show 9 in {k | k ∈ Finset.Icc 1 9 ∧ 2016 % k = 0}
            constructor
            · norm_num
            · norm_num
      rw [h1]
      rw [Set.ncard_eq_toFinset_card']
      native_decide
  · -- Show no smaller element is in the set
    intro N hN
    rcases hN with ⟨h1, h2⟩
    unfold is_Immortals at h2
    by_contra h
    push_neg at h
    have h3 : N < 2016 := h
    -- For each possible value of N between 2000 and 2015, show that the set is smaller than 8
    have h4 : {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0}.ncard ≥ 8 := h2
    have h6 : {k | k ∈ Finset.Icc 1 9 ∧ N % k = 0} = Finset.filter (fun k => N % k = 0) (Finset.Icc 1 9) := by
      ext k
      simp
    rw [h6] at h4
    rw [Set.ncard_coe_Finset] at h4
    interval_cases N <;> try { 
      contradiction
    } <;> try { 
      omega
    }