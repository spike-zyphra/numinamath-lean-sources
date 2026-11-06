import Mathlib

theorem number_theory_8025 : {m : ℤ | 417 % (m + 2011) = 0}.encard = 8 := by
  have h1 : {m : ℤ | 417 % (m + 2011) = 0} = {-2428, -2150, -2014, -2012, -2010, -2008, -1872, -1594} := by 
    ext m
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
    constructor
    · -- Forward direction: if 417 % (m + 2011) = 0, then m must be in the set
      intro h
      have h2 : m + 2011 ∣ 417 := by 
        exact Int.dvd_of_emod_eq_zero h
      have h3 : m + 2011 ≤ 417 := by 
        apply Int.le_of_dvd (by norm_num)
        exact h2
      have h4 : m + 2011 ≥ -417 := by 
        have h5 : -(m + 2011) ∣ 417 := by 
          exact Int.neg_dvd.2 h2
        have h6 : -(m + 2011) ≤ 417 := by 
          apply Int.le_of_dvd (by norm_num)
          exact h5
        linarith
      have h6 : m + 2011 = 1 ∨ m + 2011 = 3 ∨ m + 2011 = 139 ∨ m + 2011 = 417 ∨ m + 2011 = -1 ∨ m + 2011 = -3 ∨ m + 2011 = -139 ∨ m + 2011 = -417 := by 
        interval_cases k : m + 2011 <;> norm_num at *
        <;> try { tauto }
        <;> omega
      rcases h6 with h2 | h2 | h2 | h2 | h2 | h2 | h2 | h2
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
      · 
        omega
    · -- Backward direction: if m is in the set, then 417 % (m + 2011) = 0
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- m = -2428
        norm_num
      · -- m = -2150
        norm_num
      · -- m = -2014
        norm_num
      · -- m = -2012
        norm_num
      · -- m = -2010
        norm_num
      · -- m = -2008
        norm_num
      · -- m = -1872
        norm_num
      · -- m = -1594
        norm_num
  rw [h1]
  rw [Set.encard]
  simp [Set.ncard_insert_of_not_mem, Set.ncard_singleton]
  <;> rfl