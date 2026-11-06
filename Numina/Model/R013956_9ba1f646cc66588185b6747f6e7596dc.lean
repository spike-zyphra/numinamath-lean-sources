import Mathlib

theorem number_theory_282232 :
    Set.ncard {n : ℕ | ∃ k, n ∈ Finset.Icc 100 999 ∧ n = k + 17 ∧ ∃ m, m ∈ Finset.Icc 10 99 ∧ n = m + 17} = 17 := by
  have h1 : {n : ℕ | ∃ k, n ∈ Finset.Icc 100 999 ∧ n = k + 17 ∧ ∃ m, m ∈ Finset.Icc 10 99 ∧ n = m + 17} = Set.Icc 100 116 := by 
    ext n
    simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_Icc]
    constructor 
    · -- First prove `→` direction (n in set S means n in Icc 100 116)
      rintro ⟨k, ⟨hn1, hn2⟩, h1, m, ⟨hm1, hm2⟩, h2⟩
      omega 
    · -- Prove `←` direction (n in Icc 100 116 means n in set S)
      rintro ⟨hn1, hn2⟩ 
      refine' ⟨n - 17, ⟨by omega, by omega⟩, by omega, n - 17, ⟨by omega, by omega⟩, by omega⟩
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  native_decide