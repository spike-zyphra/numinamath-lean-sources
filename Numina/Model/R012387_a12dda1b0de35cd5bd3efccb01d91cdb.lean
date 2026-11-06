import Mathlib

theorem number_theory_264935 :
    Set.ncard {x : ℕ | 0 < x ∧ x < 100 ∧ ∃ k : ℤ, Real.sqrt (1 + 2 + 3 + 4 + x) = k} = 7 := by
  have h1 : {x : ℕ | 0 < x ∧ x < 100 ∧ ∃ k : ℤ, Real.sqrt (1 + 2 + 3 + 4 + x) = k} = {6, 15, 26, 39, 54, 71, 90} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume h
      rintro ⟨hx1, hx2, ⟨k, hk⟩⟩
      have h2 : (1 + 2 + 3 + 4 + (x : ℝ)) = (k : ℝ) ^ 2 := by
        have h3 : Real.sqrt (1 + 2 + 3 + 4 + (x : ℝ)) = (k : ℝ) := by
          simpa using hk
        calc
          (1 + 2 + 3 + 4 + (x : ℝ)) = (Real.sqrt (1 + 2 + 3 + 4 + (x : ℝ))) ^ 2 := by rw [Real.sq_sqrt]; positivity
          _ = (k : ℝ) ^ 2 := by rw [h3]
      have h4 : k ^ 2 = (10 + x : ℤ) := by 
        have h5 : (1 + 2 + 3 + 4 + (x : ℝ)) = (k : ℝ) ^ 2 := h2
        have h5' : (10 + (↑x : ℝ)) = (k : ℝ) ^ 2 := by
          linarith
        have h6 : (10 + (x : ℤ) : ℤ) = (k ^ 2 : ℤ) := by
          have h7 : (10 + (↑x : ℝ) : ℝ) = (k : ℝ) ^ 2 := h5'
          have h8 : (k ^ 2 : ℝ) = (k ^ 2 : ℤ) := by
            simp
          have h9 : (k : ℝ) ^ 2 = (k ^ 2 : ℤ) := by
            simp
          have h10 : (10 + (↑x : ℝ) : ℝ) = (10 + (x : ℤ) : ℤ) := by
            simp
          rw [h10] at h7
          exact_mod_cast h7
        ring_nf at h6 ⊢
        all_goals omega
      have h5 : k ≥ 0 := by
        by_contra h
        push_neg at h
        have hk1 : k < (0 : ℤ) := by linarith
        have h6 : (k : ℝ) < (0 : ℝ) := by exact_mod_cast hk1
        have h7 : Real.sqrt (1 + 2 + 3 + 4 + (x : ℝ)) ≥ 0 := by 
          positivity
        have h8 : (k : ℝ) ≥ (0 : ℝ) := by 
          linarith [h7, hk]
        linarith
      have h6 : k ≤ (10 : ℤ) := by
        by_contra h7
        push_neg at h7
        have hk11 : k ≥ 11 := by
          omega
        nlinarith [h4, hk11, show (x : ℤ) < 100 by omega]
      have h7 : k ≥ (4 : ℤ) := by
        by_contra h8
        push_neg at h8
        have hk11 : k ≤ 3 := by
          omega
        nlinarith [h4, hk11, show (x : ℤ) > 0 by omega]
      interval_cases k <;> norm_num at h4 
      <;> omega
    · -- Show that these x make sqrt integer
      rintro (rfl | rfl | rfl | rfl | rfl | rfl | rfl)
      · -- x = 6
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 4 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- x = 15
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 5 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- x = 26
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 6 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- x = 39
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 7 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- x = 54
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 8 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- x = 71
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 9 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
      · -- x = 90
        constructor
        · norm_num 
        constructor
        · norm_num 
        · use 10 
          rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  rw [h1]
  rw [Set.ncard_eq_toFinset_card']
  simp [Set.toFinset]
  <;> try { native_decide }