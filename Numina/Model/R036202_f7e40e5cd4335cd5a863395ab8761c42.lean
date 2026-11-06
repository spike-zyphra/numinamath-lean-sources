import Mathlib

theorem number_theory_3712 :
    Set.ncard {a : ℤ | ∃ n, a = n ∧ IsSquare (n * (n + 1) * (n + 2) * (n + 3))} = 4 := by 
  have h1 : {a : ℤ | ∃ n, a = n ∧ IsSquare (n * (n + 1) * (n + 2) * (n + 3))} = {-3, -2, -1, 0} := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · -- Assume n in left side set
      rintro ⟨n, hn, h1⟩
      rw [hn] at *
      rcases h1 with ⟨k, hk⟩
      have h2 : n * (n + 1) * (n + 2) * (n + 3) = k ^ 2 := by
        nlinarith
      have h4 : n * (n + 1) * (n + 2) * (n + 3) = (n ^ 2 + 3 * n) * (n ^ 2 + 3 * n + 2) := by 
        ring
      rw [h4] at h2
      have h5 : (n ^ 2 + 3 * n : ℤ) * (n ^ 2 + 3 * n + 2) = k ^ 2 := h2
      have h6 : ((n ^ 2 + 3 * n : ℤ) + 1) ^ 2 - k ^ 2 = 1 := by
        nlinarith
      have h7 : ((n ^ 2 + 3 * n + 1) - k) * ((n ^ 2 + 3 * n + 1) + k) = 1 := by 
        nlinarith [h6]
      have h8 : (n ^ 2 + 3 * n + 1 - k : ℤ) ∣ 1 := by 
        use (n ^ 2 + 3 * n + 1 + k)
        <;> linarith [h7]
      have h9 : (n ^ 2 + 3 * n + 1 - k : ℤ) = 1 ∨ (n ^ 2 + 3 * n + 1 - k : ℤ) = -1 := by
        have h10 : (n ^ 2 + 3 * n + 1 - k : ℤ) ∣ 1 := h8
        have h11 : (n ^ 2 + 3 * n + 1 - k : ℤ) = 1 ∨ (n ^ 2 + 3 * n + 1 - k : ℤ) = -1 := by
          have h12 : (n ^ 2 + 3 * n + 1 - k : ℤ) ≤ 1 := by 
            exact Int.le_of_dvd (by norm_num) h10
          have h13 : (n ^ 2 + 3 * n + 1 - k : ℤ) ≥ -1 := by
            have h14 : (- (n ^ 2 + 3 * n + 1 - k) : ℤ) ∣ 1 := by
              exact Int.neg_dvd.2 h10
            have h15 : (- (n ^ 2 + 3 * n + 1 - k) : ℤ) ≤ 1 := by 
              exact Int.le_of_dvd (by norm_num) h14
            omega
          interval_cases h : (n ^ 2 + 3 * n + 1 - k : ℤ) <;> tauto
        tauto
      rcases h9 with h9 | h9
      · -- Case 1
        have h10 : (n ^ 2 + 3 * n + 1 + k : ℤ) = 1 := by 
          nlinarith [h7, h9]
        have h11 : (n ^ 2 + 3 * n : ℤ) = 0 := by
          nlinarith [h9, h10]
        have h13 : n * (n + 3) = 0 := by
          nlinarith [h11]
        have h14 : n = 0 ∨ n = -3 := by
          cases' (mul_eq_zero.mp h13) with h15 h16
          · -- Case left
            left
            linarith
          · -- Case right
            right
            linarith
        tauto
      · -- Case 2
        have h10 : (n ^ 2 + 3 * n + 1 + k : ℤ) = -1 := by 
          nlinarith [h7, h9]
        have h11 : (n ^ 2 + 3 * n : ℤ) = -2 := by
          nlinarith [h9, h10]
        have h13 : (n + 1) * (n + 2) = 0 := by 
          nlinarith [h11]
        have h14 : n = -1 ∨ n = -2 := by
          cases' (mul_eq_zero.mp h13) with h15 h16
          · -- Case left
            left
            linarith
          · -- Case right
            right
            linarith
        tauto
    · -- Assume n in right side set
      rintro (rfl | rfl | rfl | rfl)
      · -- n = -3
        refine ⟨-3, by norm_num, ?_⟩
        native_decide
      · -- n = -2
        refine ⟨-2, by norm_num, ?_⟩
        native_decide
      · -- n = -1
        refine ⟨-1, by norm_num, ?_⟩
        native_decide
      · -- n = 0
        refine ⟨0, by norm_num, ?_⟩
        native_decide
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp
  <;> try { native_decide }