import Mathlib

theorem number_theory_306896 :
    ∑ᶠ m ∈ {x : ℕ | 0 < x ∧ ∃ k : ℤ, Real.sqrt (x ^ 2 + 1203) = k}, m = 800 := by
  have h1 : {x : ℕ | 0 < x ∧ ∃ k : ℤ, Real.sqrt (x ^ 2 + 1203) = k} = {199, 601} := by
    ext x 
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- First direction: if x is in the set, then x ∈ {199, 601}
      rintro ⟨hx1, ⟨k, hk⟩⟩
      have h2 : (k : ℝ) ^ 2 = x ^ 2 + (1203 : ℝ) := by
        calc
          (k : ℝ) ^ 2 = (Real.sqrt (x ^ 2 + 1203 : ℝ)) ^ 2 := by rw [hk]
          _ = x ^ 2 + (1203 : ℝ) := by
            rw [Real.sq_sqrt]
            positivity
      have h3 : k ^ 2 = x ^ 2 + 1203 := by
        have h4 : (k : ℝ) ^ 2 = (x : ℝ) ^ 2 + (1203 : ℝ) := by
          simpa using h2
        have h5 : (k : ℤ) ^ 2 = (x : ℤ) ^ 2 + (1203 : ℤ) := by
          exact_mod_cast (show (k : ℝ) ^ 2 = (x : ℝ) ^ 2 + (1203 : ℝ) by linarith)
        exact_mod_cast h5
      have h4 : k ≥ 0 := by
        by_contra h
        push_neg at h
        have hk2 : k < (0 : ℤ) := by omega
        have hk1 : (k : ℝ) < (0 : ℝ) := by exact_mod_cast hk2
        have hk2_eq : Real.sqrt (x ^ 2 + (1203 : ℝ) ) ≥ 0 := Real.sqrt_nonneg (x ^ 2 + (1203 : ℝ) )
        nlinarith
      have h6 : k > (x : ℤ) := by
        by_contra h
        push_neg at h
        have h8 : k ≤ (x : ℤ) := by omega
        nlinarith [show (k : ℤ) ≥ 0 by omega, sq_nonneg ((k : ℤ) - (x : ℤ)), sq_nonneg ((k : ℤ) + (x : ℤ))]
      have h7 : (k - (x : ℤ) ) * (k + (x : ℤ) ) = 1203 := by
        nlinarith
      have h9 : k - (x : ℤ) > 0 := by
        nlinarith
      have h10 : k + (x : ℤ) > 0 := by
        nlinarith [h6, show (k : ℤ) > 0 by nlinarith [show (k : ℤ) ≥ 0 by omega, show (x : ℤ) ≥ 1 by omega]]
      have h11 : k - (x : ℤ) ∣ (1203 : ℤ) := by
        use (k + (x : ℤ) )
        all_goals linarith
      have h12 : k - (x : ℤ) = 1 ∨ k - (x : ℤ) = 3 ∨ k - (x : ℤ) = 401 ∨ k - (x : ℤ) = 1203 := by
        have h13 : k - (x : ℤ) ∣ (1203 : ℤ) := h11
        have h14 : k - (x : ℤ) > 0 := h9
        have h15 : (k - (x : ℤ) ) ≤ 1203 := by
          exact Int.le_of_dvd (by omega) h13
        interval_cases h : k - (x : ℤ) <;> omega
      rcases h12 with (h12 | h12 | h12 | h12)
      · -- Case k - x = 1, so k + x = 1203
        have h13 : k + (x : ℤ) = 1203 := by
          nlinarith
        have hk1 : k = 602 := by
          nlinarith
        have hx : (x : ℤ) = 601 := by
          nlinarith
        have hx2 : x = 601 := by 
          omega
        rw [hx2]
        all_goals norm_num
      · -- Case k - x = 3, so k + x = 401
        have h14 : k + (x : ℤ) = 401 := by
          nlinarith
        have hk1 : k = 202 := by
          nlinarith
        have hx : (x : ℤ) = 199 := by
          nlinarith
        have hx2 : x = 199 := by 
          omega
        rw [hx2]
        all_goals norm_num
      · -- Case k - x = 401, so k + x = 3
        have h15 : k + (x : ℤ) = 3 := by
          nlinarith
        have h16 : (x : ℤ) < (0 : ℤ) := by
          nlinarith
        have h17 : (x : ℤ) > (0 : ℤ) := by
          have h11 : x > (0 : ℕ) := hx1
          omega
        nlinarith
      · -- Case k - x = 1203, so k + x = 1
        have h16 : k + (x : ℤ) = 1 := by
          nlinarith
        have h17 : (x : ℤ) < (0 : ℤ) := by
          nlinarith
        have h18 : (x : ℤ) > (0 : ℤ) := by
          have h11 : x > (0 : ℕ) := hx1
          omega
        nlinarith
    · -- Second direction: if x ∈ {199, 601}, then x is in the set
      rintro (rfl | rfl)
      · -- First 199
        constructor
        · norm_num
        · use 202
          have h202 : Real.sqrt (199 ^ 2 + (1203 : ℝ) ) = (202 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          exact_mod_cast h202
      · -- Then 601
        constructor
        · norm_num
        · use 602
          have h602 : Real.sqrt (601 ^ 2 + (1203 : ℝ) ) = (602 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          exact_mod_cast h602
  rw [h1]
  rw [finsum_mem_pair (by norm_num)]
  all_goals norm_num