import Mathlib

theorem algebra_6405 : ∑ᶠ x ∈ {x : ℤ | 0 < x ∧ ∃ n : ℤ, Real.sqrt (x ^ 2 + 32) = n}, x = 9 := by
  have h1 : {x : ℤ | 0 < x ∧ ∃ n : ℤ, Real.sqrt (x ^ 2 + 32) = n} = {2, 7} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, and_imp]
    constructor
    · -- Assume x is in the left side, prove it is in the right
      rintro ⟨hx_pos, ⟨n, hn⟩⟩
      have h2 : (Real.sqrt (x ^ 2 + 32) : ℝ) = (n : ℝ) := by
        simpa using hn
      have h3 : (x ^ 2 + 32 : ℝ) = (n : ℝ) ^ 2 := by
        calc
          (x ^ 2 + 32 : ℝ) = (Real.sqrt (x ^ 2 + 32) : ℝ) ^ 2 := by
            rw [Real.sq_sqrt]
            positivity
          _ = (n : ℝ) ^ 2 := by
            rw [h2]
      have h4 : (x ^ 2 + 32 : ℤ) = (n ^ 2 : ℤ) := by
        exact_mod_cast (show (x ^ 2 + 32 : ℝ) = (n : ℝ) ^ 2 from h3)
      have h5 : x ^ 2 + 32 = n ^ 2 := by
        exact_mod_cast h4
      have h6 : n ^ 2 - x ^ 2 = 32 := by
        nlinarith
      have h7 : (n - x) * (n + x) = 32 := by
        nlinarith
      have h8 : n - x ∣ 32 := by
        use n + x
        all_goals nlinarith
      have h9 : n - x ≤ 32 := by
        apply Int.le_of_dvd (by norm_num) h8
      have h10 : n - x ≥ -32 := by
        have h11 : - (n - x) ∣ 32 := by
          exact Int.neg_dvd.2 h8
        have h12 : - (n - x) ≤ 32 := by
          apply Int.le_of_dvd (by norm_num) h11
        omega
      interval_cases h : n - x <;> try { 
        omega 
      } <;> try { 
          norm_num at h7 h8 h9 h10 
          all_goals 
            have : x ≤ 32 := by nlinarith 
            have : x ≥ 0 := by linarith 
            interval_cases x <;> try { 
              omega 
            } <;> try { 
                norm_num at h5 h6 
                all_goals 
                  try { 
                    have : n ≤ 32 := by nlinarith 
                    have : n ≥ -32 := by nlinarith 
                    interval_cases n <;> norm_num at h5 h6 <;> tauto 
                  } 
              } 
        }
    · -- Assume x is in the right side {2, 7}, prove it is in the left
      rintro (rfl | rfl)
      · -- Let x=2
        constructor
        · norm_num
        · -- Show exists integer n
          use 6
          have h1 : Real.sqrt (2 ^ 2 + 32 : ℝ) = (6 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          exact_mod_cast h1
      · -- Let x=7
        constructor
        · norm_num
        · -- Show exists integer n
          use 9
          have h2 : Real.sqrt (7 ^ 2 + 32 : ℝ) = (9 : ℝ) := by
            rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
          exact_mod_cast h2
  rw [h1]
  rw [finsum_mem_pair]
  all_goals norm_num