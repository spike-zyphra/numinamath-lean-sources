import Mathlib

theorem number_theory_160716 :
    {z : ℕ | z ∈ Finset.Icc 100 999 ∧ ∃n, z = ∑ i ∈ Finset.range n, n ^ i} = 
    {781} := by
  ext z
  simp only [Finset.mem_Icc, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · -- First, prove the forward direction: if z is in the set, then z = 781
    rintro ⟨⟨hz1, hz2⟩, ⟨n, hn⟩⟩
    have h1 : n ≥ 1 := by
      by_contra h
      push_neg at h
      interval_cases n <;> simp [Finset.sum_range_succ] at hn <;> omega
    have h2 : n ≤ 5 := by 
      by_contra h
      push_neg at h 
      -- Now n > 5.
      have h3 : ∑ i in Finset.range n, n ^ i ≥ ∑ i in Finset.range 6, n ^ i := by 
        have h4 : Finset.range 6 ⊆ Finset.range n := by 
          intro i hi
          simp at hi ⊢
          omega
        apply Finset.sum_le_sum_of_subset_of_nonneg h4
        · -- Show that for all i in range 6, n ^ i ≤ n ^ i
          intro i hi
          simp 
      have h4 : ∑ i in Finset.range 6, n ^ i > 999 := by 
        have eq1 : ∑ i in Finset.range 6, n ^ i = 1 + n + n ^ 2 + n ^ 3 + n ^ 4 + n ^ 5 := by 
          simp [Finset.sum_range_succ]
        rw [eq1]
        have hn1 : n ≥ 6 := by omega 
        have h8 : 1 + n + n ^ 2 + n ^ 3 + n ^ 4 + n ^ 5 ≥ 1 + 6 + 6 ^ 2 + 6 ^ 3 + 6 ^ 4 + 6 ^ 5 := by
          have hn1 : n ≥ 6 := by omega 
          have h9 : n ^ 2 ≥ 6 ^ 2 := by nlinarith
          have h10 : n ^ 3 ≥ 6 ^ 3 := by nlinarith
          have h11 : n ^ 4 ≥ 6 ^ 4 := by nlinarith
          have h12 : n ^ 5 ≥ 6 ^ 5 := by nlinarith
          nlinarith
        have h9 : 1 + 6 + 6 ^ 2 + 6 ^ 3 + 6 ^ 4 + 6 ^ 5 > 999 := by 
          norm_num 
        linarith 
      have h5 : z > 999 := by
        linarith [hn, h3, h4]
      linarith 
    interval_cases n <;> try { 
      norm_num [Finset.sum_range_succ] at hn 
      <;> omega 
    }
  · -- Backward direction: if z = 781 then it is in the set
    intro h
    rw [h]
    constructor
    · -- Show 781 is in the range [100, 999]
      norm_num
    · -- Show that there exists an n such that 781 = ∑ i in Finset.range n, n ^ i
      use 5
      native_decide