import Mathlib
theorem number_theory_609246 : {n : ℤ | n ^ 2 - 4 ≠ 0 ∧ (∃ k : ℤ, (n ^ 3 + 8) / ((↑n : ℝ) ^ 2 - 4) = k)} = {0, 1, 3, 4, 6}:= by
  ext n
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.union_insert,
    Set.union_singleton]
  constructor
  · -- Forward direction: assuming n is in the left side set, proving it's in the right side set
    rintro ⟨h1, ⟨k, hk⟩⟩
    have h2 : (n ^ 3 + 8 : ℝ) / ((n : ℝ) ^ 2 - 4) = (k : ℝ) := by
      simpa using hk
    have h3 : (n ^ 3 + 8 : ℝ) = (k : ℝ) * ((n : ℝ) ^ 2 - 4) := by 
      field_simp [(show (n : ℝ) ^ 2 - 4 ≠ 0 by 
        by_contra h
        have : n ^ 2 - 4 = 0 := by 
          have : (n : ℝ) ^ 2 - 4 = (0 : ℝ) := by linarith
          have : (n : ℝ) ^ 2 = (4 : ℝ) := by linarith
          have : (n ^ 2 : ℝ) = (4 : ℝ) := by linarith
          have : (n ^ 2 : ℤ) = (4 : ℤ) := by
            exact_mod_cast this
          linarith
        contradiction
      )] at h2 ⊢
      linarith
    have h4 : (n ^ 3 + 8 : ℤ) = (k : ℤ) * ((n : ℤ) ^ 2 - 4) := by
      exact_mod_cast h3
    have h5 : (n ^ 3 + 8 : ℤ) = k * (n^2 - 4) := by 
      linarith [h4]
    have h6 : (k - n) * (n ^ 2 - 4) = 4 * n + 8 := by 
      linarith [h5]
    have h7 : (n + 2 : ℤ) ≠ 0 := by 
      by_contra h
      have h8 : n = -2 := by linarith
      have h9 : n ^ 2 - 4 = 0 := by 
        rw [h8]
        norm_num
      contradiction
    have h8 : (k - n) * (n - 2) = 4 := by
      have h9 : (n + 2 : ℤ) ≠ 0 := h7
      have h11 : (k - n) * (n ^ 2 - 4) = 4 * n + 8 := h6
      have h12 : n ^ 2 - 4 = (n - 2) * (n + 2) := by 
        ring
      rw [h12] at h11
      have h13 : (k - n) * (n - 2) = 4 := by 
        apply (mul_left_inj' h7).mp
        linarith
      linarith
    have h9 : (n - 2) ∣ 4 := by 
      use (k - n)
      linarith [h8]
    have h10 : (n - 2) ≤ 4 := by 
      apply Int.le_of_dvd (by norm_num) h9
    have h11 : (n - 2) ≥ -4 := by 
      have h14 : (- (n - 2)) ∣ 4 := by 
        exact Int.neg_dvd.2 h9
      have h15 : (- (n - 2)) ≤ 4 := by 
        apply Int.le_of_dvd (by norm_num) h14
      have : (n - 2) ≥ -4 := by 
        omega
      linarith
    have h14 : n ≥ -2 := by 
      linarith
    have h15 : n ≤ 6 := by 
      linarith
    interval_cases n <;> norm_num at h1 h4 h6 h8 h9 h10 h11 h14 h15 ⊢
    <;> omega
  · -- Backward direction: assuming n is in the right side set, proving it's in the left side set
    intro h
    rcases h with (rfl | rfl | rfl | rfl | rfl)
    · constructor
      · norm_num
      · use -2
        norm_num
    · constructor
      · norm_num
      · use -3
        norm_num
    · constructor
      · norm_num
      · use 7
        norm_num
    · constructor
      · norm_num
      · use 6
        norm_num
    · constructor
      · norm_num
      · use 7
        norm_num