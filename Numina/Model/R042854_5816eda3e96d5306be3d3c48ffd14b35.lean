import Mathlib

theorem number_theory_108828 : {a + b + c | (a : ℤ) (b : ℤ) (c : ℤ) (h : a * b * c = -5)} = {5,-3,-7} := by 
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert, Set.union_singleton]
  constructor
  · -- Assume x ∈ {a + b + c | (a : ℤ) (b : ℤ) (c : ℤ) (h : a * b * c = -5)}
    rintro ⟨a, b, c, h, rfl⟩
    have h1 : a ∣ -5 := by
      use b * c
      all_goals nlinarith
    have h2 : b ∣ -5 := by
      use a * c
      all_goals nlinarith
    have h3 : c ∣ -5 := by
      use a * b
      all_goals nlinarith
    have h4 : a ∣ 5 := by 
      exact Int.dvd_neg.mp h1
    have h5 : b ∣ 5 := by 
      exact Int.dvd_neg.mp h2
    have h6 : c ∣ 5 := by 
      exact Int.dvd_neg.mp h3
    have h7 : a ≤ 5 := by 
      apply Int.le_of_dvd (by norm_num) h4
    have h8 : a ≥ -5 := by 
      have h8 : -a ∣ 5 := by 
        exact Int.neg_dvd.2 h4
      have h9 : -a ≤ 5 := by 
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : -a ≥ -5 := by 
        omega
      omega
    have h9 : b ≤ 5 := by 
      apply Int.le_of_dvd (by norm_num) h5
    have h10 : b ≥ -5 := by 
      have h8 : -b ∣ 5 := by 
        exact Int.neg_dvd.2 h5
      have h9 : -b ≤ 5 := by 
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : -b ≥ -5 := by 
        omega
      omega
    have h11 : c ≤ 5 := by 
      apply Int.le_of_dvd (by norm_num) h6
    have h12 : c ≥ -5 := by 
      have h8 : -c ∣ 5 := by 
        exact Int.neg_dvd.2 h6
      have h9 : -c ≤ 5 := by 
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : -c ≥ -5 := by 
        omega
      omega
    interval_cases a <;> interval_cases b <;> omega 
  · -- Assume x ∈ {5, -3, -7}, need to show x ∈ {a + b + c | ...}
    rintro (rfl | rfl | rfl)
    · -- x = 5
      refine ⟨1, -1, 5, by norm_num, by norm_num⟩
    · -- x = -3
      refine ⟨1, 1, -5, by norm_num, by norm_num⟩
    · -- x = -7
      refine ⟨-1, -1, -5, by norm_num, by norm_num⟩