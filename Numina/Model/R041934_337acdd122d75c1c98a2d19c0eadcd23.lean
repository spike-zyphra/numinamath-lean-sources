import Mathlib

theorem number_theory_23042 :
    ∑ᶠ x ∈ {x : ℤ | (2 * x - 23) ∣ 67}, x = 46 := by
  have h1 : {x : ℤ | (2 * x - 23) ∣ 67} = {-22, 11, 12, 45} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Assume h : (2 * x - 23) ∣ 67, prove x ∈ {-22, 11, 12, 45}
      intro h
      have h2 : (2 * x - 23) ∣ 67 := h
      have h3 : (2 * x - 23) ≤ 67 := by 
        apply Int.le_of_dvd (by norm_num) h2
      have h4 : (2 * x - 23) ≥ -67 := by
        have h5 : (- (2 * x - 23)) ∣ 67 := by 
          exact Int.neg_dvd.2 h2
        have h6 : - (2 * x - 23) ≤ 67 := by 
          apply Int.le_of_dvd (by norm_num) h5
        omega
      have h5 : x ≤ 45 := by 
        omega
      have h6 : x ≥ -22 := by 
        omega
      interval_cases x <;> norm_num at h2 ⊢ <;> tauto
    · -- Assume x ∈ {-22, 11, 12, 45}, prove h : (2 * x - 23) ∣ 67
      rintro (rfl | rfl | rfl | rfl)
      · norm_num
      · norm_num
      · norm_num
      · norm_num
  rw [h1]
  rw [finsum_mem_insert, finsum_mem_insert, finsum_mem_insert, finsum_mem_singleton]
  all_goals norm_num
  <;> try { tauto }