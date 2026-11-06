import Mathlib
theorem algebra_611164 : {m : ℤ | ∃ k : ℤ, k ^ 2 = m ^ 2 + 6 * m + 28} = {6, -12}:= by
  ext m
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
  constructor
  · -- Assume there's a k such that k^2 = m^2 + 6 m + 28
    rintro ⟨k, hk⟩
    have h1 : k ^ 2 = (m + 3) ^ 2 + 19 := by
      nlinarith
    have h2 : (k - (m + 3)) * (k + (m + 3)) = 19 := by
      nlinarith [h1]
    have h3 : k - (m + 3) ∣ 19 := by
      use k + (m + 3)
      linarith
    have h4 : k - (m + 3) = 1 ∨ k - (m + 3) = 19 ∨ k - (m + 3) = -1 ∨ k - (m + 3) = -19 := by 
      have h3' : k - (m + 3) ∣ 19 := h3
      have h3pos : k - (m + 3) ≤ 19 := by 
        exact Int.le_of_dvd (by norm_num) h3'
      have h3neg : k - (m + 3) ≥ -19 := by
        have h3neg' : -(k - (m + 3)) ∣ 19 := by 
          exact Int.neg_dvd.2 h3'
        have h3neg'' : -(k - (m + 3)) ≤ 19 := by 
          exact Int.le_of_dvd (by norm_num) h3neg'
        linarith
      interval_cases (k - (m + 3)) <;> tauto 
    rcases h4 with h4 | h4 | h4 | h4 
    · -- Let k - (m + 3) = 1
      have h5 : k + (m + 3) = 19 := by 
        rw [show k - (m + 3) = 1 by linarith [h4] ] at h2
        linarith 
      have h6 : m = 6 := by 
        omega 
      simp [h6] 
    · -- Let k - (m + 3) = 19 
      have h5 : k + (m + 3) = 1 := by 
        rw [show k - (m + 3) = 19 by linarith [h4] ] at h2
        linarith 
      have h6 : m = -12 := by 
        omega 
      simp [h6] 
    · -- Let k - (m + 3) = -1 
      have h5 : k + (m + 3) = -19 := by 
        rw [show k - (m + 3) = -1 by linarith [h4] ] at h2
        linarith 
      have h6 : m = -12 := by 
        omega 
      simp [h6] 
    · -- Let k - (m + 3) = -19 
      have h5 : k + (m + 3) = -1 := by 
        rw [show k - (m + 3) = -19 by linarith [h4] ] at h2
        linarith 
      have h6 : m = 6 := by 
        omega 
      simp [h6] 
  · -- Show that there exists k
    rintro (rfl | rfl)
    · -- m = 6 
      use 10 
      norm_num 
    · -- m = -12 
      use 10 
      norm_num