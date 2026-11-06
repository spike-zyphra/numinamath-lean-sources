import Mathlib

theorem other_34500 (x : ℝ) :
    ⌊x⌋^5 + (x - ⌊x⌋)^5 = x^5 ↔ x ∈ Set.Ico 0 1 ∪ Set.range Int.cast := by
  constructor
  · -- First implication: if the equation holds, then x ∈ [0, 1) ∪ ℤ
    intro h_eq
    have h1 : (⌊x⌋ : ℝ) ≤ x := by exact Int.floor_le x
    have h2 : x < (⌊x⌋ + 1 : ℝ) := by exact Int.lt_floor_add_one x
    have h3 : (x - (⌊x⌋ : ℝ) ) ≥ 0 := by nlinarith 
    have h4 : (x - (⌊x⌋ : ℝ) ) < 1 := by nlinarith
    have h5 : (⌊x⌋ : ℝ) ^ 5 + (x - (⌊x⌋ : ℝ) ) ^ 5 = x ^ 5 := by 
      simpa using h_eq 
    by_cases h6 : ⌊x⌋ = 0 
    · -- If ⌊x⌋ = 0 
      have h7 : (⌊x⌋ : ℝ) = (0 : ℝ) := by 
        rw [show ⌊x⌋ = (0 : Int) by exact_mod_cast h6]
        all_goals norm_num 
      have hx1 : x ≥ 0 := by 
        nlinarith [h7, h1]
      have hx2 : x < 1 := by 
        nlinarith [h7, h2]
      simp [Set.mem_union, Set.mem_Ico, hx1, hx2]
      all_goals norm_num 
      all_goals try { tauto }
    · -- ⌊x⌋ ≠ 0 
      have h8 : ⌊x⌋ ≠ 0 := by 
        exact h6 
      have h9 : (⌊x⌋ : ℝ) ≠ 0 := by 
        intro h 
        have : ⌊x⌋ = 0 := by 
          norm_num at h ⊢ 
          <;> try { 
            have hn : ⌊x⌋ = 0 := by 
              exact_mod_cast (show (⌊x⌋ : ℝ) = (0 : ℝ) by linarith)
            assumption
          } 
          <;> try { tauto } 
        tauto 
      -- Show x = ⌊x⌋.
      have h10 : (x - (⌊x⌋ : ℝ) ) = 0 := by
        set n : ℝ := (⌊x⌋ : ℝ)
        have hn1 : n ≠ 0 := h9
        have eq1 : n ^ 5 + (x - n) ^ 5 = x ^ 5 := by 
          simpa using h5
        have eq2 : (x - n) ^ 5 + n ^ 5 = (n + (x - n)) ^ 5 := by
          have h_eq6 : n + (x - n) = x := by
            nlinarith
          rw [h_eq6] at *
          all_goals linarith [h_eq6]
          all_goals linarith
        -- simplify eq2 to get 5 * n * (x - n) * x^3
        have eq3 : (x - n) * (5 * n * ((n + (x - n)) ^ 3)) = 0 := by
          nlinarith [sq_nonneg (x - n), sq_nonneg (n), sq_nonneg ((n : ℝ) + (x - n)), sq_nonneg ((n : ℝ) ^ 2), sq_nonneg ((x - n) ^ 2), sq_pos_of_ne_zero hn1]
        cases' (mul_eq_zero.mp eq3) with h11 h12
        · -- x - n = 0 
          linarith 
        · -- 5 * n * ((n + (x - n)) ^ 3) = 0 
          have h_eq6 : n + (x - n) = x := by 
            nlinarith 
          rw [h_eq6] at h12
          have h_eq7 : 5 * n * (x ^ 3) = 0 := by
            nlinarith
          cases' (mul_eq_zero.mp h_eq7) with h14 h15 
          · -- 5 * n = 0 
            have hn2 : n = 0 := by 
              nlinarith 
            tauto -- Contradicts hn1 : n ≠ 0
          · -- x ^ 3 = 0 
            have hx3 : x = 0 := by 
              have : x^3 = 0 := by 
                linarith 
              have hx4 : x ^ 3 = 0 := this
              have hx5 : x = 0 := by 
                have h_eq6 : x ^ 3 = 0 := hx4
                simp at h_eq6 ⊢ 
                nlinarith 
                all_goals nlinarith 
              assumption
            have hn4 : n = (0 : ℝ) := by
              -- n ≤ x < n + 1 
              -- 0 ≤ 0 < 1
              have hn5 : ⌊x⌋ = (0 : Int) := by
                rw [show x = (0 : ℝ) by linarith]
                norm_num 
                all_goals try { tauto } 
              have hn6 : (⌊x⌋ : ℝ) = (0 : ℝ) := by
                norm_num [hn5]
                all_goals try { nlinarith }
                all_goals try { 
                  exact_mod_cast hn5
                }
              linarith [hn6]
              all_goals try { nlinarith }
            tauto -- Contradicts hn1 : n ≠ 0
      have h11 : x = (⌊x⌋ : ℝ) := by 
        linarith 
      have h12 : x ∈ Set.range Int.cast := by 
        rw [Set.mem_range]
        use ⌊x⌋ 
        all_goals norm_num at *
        all_goals try { linarith }
        all_goals try { 
          exact_mod_cast (show (x : ℝ) = (⌊x⌋ : ℝ) by linarith)
        }
      simp [Set.mem_union, h12] 
      all_goals try { tauto }
      all_goals try { norm_num }
      all_goals try { linarith }
      all_goals try { tauto }
  · -- Second implication: x ∈ [0, 1) ∪ ℤ → equation
    rintro (h | h)
    · -- h : x ∈ [0, 1)
      rcases h with ⟨hx1, hx2⟩
      have h4 : ⌊x⌋ = 0 := by 
        rw [Int.floor_eq_iff]
        constructor <;> (try norm_num) <;> linarith
      have h6 : (⌊x⌋ : ℝ) = (0 : ℝ) := by 
        rw [show ⌊x⌋ = (0 : Int) by exact_mod_cast h4]
        all_goals norm_num
      simp [h6]
      all_goals nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x ^ 3), sq_nonneg (x ^ 4)]
    · -- h : x ∈ ℤ
      rcases h with ⟨n, hn⟩
      have h4 : ⌊x⌋ = n := by
        rw [Int.floor_eq_iff]
        simp [hn] 
        all_goals linarith 
      have h6 : (⌊x⌋ : ℝ) = (n : ℝ) := by
        exact_mod_cast h4 
      -- Here we need to show x^5 = ⌊x⌋^5 + (x - ⌊x⌋)^5
      -- We know x = n (from hn). So x - ⌊x⌋ = n - n = 0.
      have h7 : (x - (⌊x⌋ : ℝ) ) = 0 := by 
        have h_eq5 : (x : ℝ) = (n : ℝ) := by 
          linarith [hn] 
        rw [h_eq5]
        simp [show (⌊x⌋ : ℝ) = (n : ℝ) by exact_mod_cast h4] 
        all_goals nlinarith 
      rw [h7]
      simp [h6]
      all_goals norm_num 
      all_goals try { 
        have eq1 : (x : ℝ) = (n : ℝ) := by linarith [hn] 
        rw [eq1] 
        all_goals norm_num 
        all_goals try { tauto }
      }
      all_goals try { nlinarith [sq_nonneg (n : ℝ), sq_nonneg (x), sq_nonneg (x ^ 2), sq_nonneg ((n : ℝ) ^ 2), sq_nonneg (x ^ 3), sq_nonneg ((n : ℝ) ^ 3), sq_nonneg (x ^ 4), sq_nonneg ((n : ℝ) ^ 4)]
      }
      all_goals try { nlinarith [sq_nonneg (n : ℝ), sq_nonneg (x - (n : ℝ)), sq_nonneg (x ^ 2), sq_nonneg ((n : ℝ) ^ 2), sq_nonneg (x ^ 3), sq_nonneg ((n : ℝ) ^ 3), sq_nonneg (x ^ 4), sq_nonneg ((n : ℝ) ^ 4)]
      }
      all_goals try { tauto }
      all_goals try { norm_num }
      all_goals try { linarith }
      all_goals try { tauto }