import Mathlib

theorem algebra_633731:
    ∑ᶠ x ∈ {x: ℤ | 0 < x ∧ ∃ m: ℤ, √(x ^ 2 + 24) = m}, x = 6 := by
  have h1 : {x: ℤ | 0 < x ∧ ∃ m: ℤ, √(x ^ 2 + 24) = m} = {1, 5} := by 
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Forward direction: if x in the set, then x in {1, 5}
      intro h
      rcases h with ⟨hx1, ⟨m, hm⟩⟩
      have h2 : (x: ℝ) ^ 2 + (24: ℝ) = (m: ℝ) ^ 2 := by
        calc
          (x: ℝ) ^ 2 + (24: ℝ) = (↑x ^ 2 + 24: ℝ) := by ring
          _ = ((√(x ^ 2 + 24): ℝ) ) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = ((m: ℝ)) ^ 2 := by rw [hm]
      have h3 : (x: ℤ) ^ 2 + 24 = (m: ℤ) ^ 2 := by
        have h2' : (x: ℝ) ^ 2 + (24: ℝ) = (m: ℝ) ^ 2 := by
          calc
            (x: ℝ) ^ 2 + (24: ℝ) = (↑x ^ 2 + 24: ℝ) := by ring
            _ = ((√(x ^ 2 + 24): ℝ) ) ^ 2 := by rw [Real.sq_sqrt]; positivity
            _ = ((m: ℝ)) ^ 2 := by rw [hm]
        norm_cast at h2'
      have h4 : m ^ 2 - x ^ 2 = 24 := by 
        linarith 
      have h5 : (m - x) * (m + x) = 24 := by 
        nlinarith 
      have h6 : (m - x) ∣ 24 := by 
        use (m + x)
        all_goals linarith 
      have h7 : (m - x) ≤ 24 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      have h8 : (m - x) ≥ -24 := by 
        have h9 : -(m - x) ∣ 24 := by 
          exact Int.neg_dvd.2 h6 
        have h10 : -(m - x) ≤ 24 := by 
          apply Int.le_of_dvd (by norm_num) h9 
        linarith 
      have h9 : (m - x) ∣ 24 := h6 
      have h99 : (m - x) ≤ 24 := h7 
      have h999 : (m - x) ≥ -24 := h8 
      have h34 : (m - x) ≤ 24 := h99 
      have h35 : (m - x) ≥ -24 := h999 
      interval_cases k : (m - x) <;> norm_num at h5 h9 h34 h35 
      <;> try { 
        omega 
      } 
    · -- Backward direction: if x ∈ {1,5}, then x in the set 
      rintro (rfl | rfl)
      · constructor 
        · norm_num 
        · use 5 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
      · constructor 
        · norm_num 
        · use 7 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num 
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num