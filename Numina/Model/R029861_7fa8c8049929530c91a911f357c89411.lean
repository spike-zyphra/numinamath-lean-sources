import Mathlib


theorem number_theory_12972 :
    ∑ᶠ n ∈ {n : ℕ | ⌊Real.logb 5 n⌋ = 1}, n = 290 := by 
  have h1 : {n : ℕ | ⌊Real.logb 5 n⌋ = 1} = Set.Icc 5 24 := by
    ext n
    simp only [Set.mem_setOf_eq, Set.mem_Icc]
    by_cases h : n > 0
    · -- If n > 0
      have h2 : (n : ℝ) > 0 := by exact_mod_cast (show n > 0 by linarith)
      constructor
      · -- Assume ⌊Real.logb 5 n⌋ = 1, prove 5 ≤ n ∧ n ≤ 24
        intro h_eq
        have h3 : 1 ≤ Real.logb 5 (n : ℝ) := by
          have h4 : ⌊Real.logb 5 (n : ℝ)⌋ = 1 := by exact_mod_cast h_eq
          have h5 : 1 ≤ Real.logb 5 (n : ℝ) := by
            have h6 : (⌊Real.logb 5 (n : ℝ)⌋ : ℝ) ≤ Real.logb 5 (n : ℝ) := by
              exact Int.floor_le (Real.logb 5 (n : ℝ))
            have h7 : (⌊Real.logb 5 (n : ℝ)⌋ : ℝ) = (1 : ℝ) := by
              exact_mod_cast h_eq
            nlinarith
          linarith
        have h8 : Real.logb 5 (n : ℝ) < (2 : ℝ) := by
          have h9 : Real.logb 5 (n : ℝ) < (⌊Real.logb 5 (n : ℝ)⌋ + 1 : ℝ) := by
            exact Int.lt_floor_add_one (Real.logb 5 (n : ℝ))
          have h10 : ⌊Real.logb 5 (n : ℝ)⌋ = 1 := by exact_mod_cast h_eq
          rw [show ⌊Real.logb 5 (n : ℝ)⌋ = (1 : ℤ) by omega] at h9
          norm_num at h9 ⊢
          linarith
        have h11 : (5 : ℝ) ≤ (n : ℝ) := by
          have h12 : Real.logb 5 (5 : ℝ) = 1 := by
            rw [Real.logb_self_eq_one]
            all_goals norm_num
          have h16 : Real.logb 5 (5 : ℝ) ≤ Real.logb 5 (n : ℝ) := by
            nlinarith
          have h180 : (5 : ℝ) ≤ (n : ℝ) := by
            by_contra h
            push_neg at h
            have h7 : (n : ℝ) < (5 : ℝ) := by nlinarith
            have h20 : Real.logb (5 : ℝ) (n : ℝ) < Real.logb (5 : ℝ) (5 : ℝ) := by
              apply Real.logb_lt_logb
              all_goals
              try { norm_num  }
              all_goals
              try {  nlinarith  }
            nlinarith
          linarith
        have h19 : (n : ℝ) < (25 : ℝ) := by
          have h18 : Real.logb 5 (n : ℝ) < (2 : ℝ) := h8
          have h10 : Real.logb 5 (25 : ℝ) = (2 : ℝ) := by
            calc
              Real.logb 5 (25 : ℝ) = Real.logb 5 ((5 : ℝ) ^ 2) := by norm_num
              _ = 2 := by simp [Real.logb_pow]
          have h100 : Real.logb 5 (n : ℝ) < Real.logb 5 (25 : ℝ) := by
            nlinarith
          have h12 : (n : ℝ) < (25 : ℝ) := by
            by_contra h
            push_neg at h
            have h7 : (n : ℝ) ≥ (25 : ℝ) := by nlinarith
            have h19 : Real.logb 5 (n : ℝ) ≥ Real.logb 5 (25 : ℝ) := by
              apply Real.logb_le_logb_of_le
              all_goals
              try { norm_num  }
              all_goals
              try {  nlinarith  }
            nlinarith
          linarith
        have h21 : n < 25 := by
          by_contra h
          push_neg at h
          have h22 : n ≥ 25 := by omega
          have h23 : (n : ℝ) ≥ (25 : ℝ) := by exact_mod_cast h22
          nlinarith
        have h24 : n ≥ 5 := by
          by_contra h
          push_neg at h
          have h24 : n < 5 := by omega
          have h24' : (n : ℝ) < (5 : ℝ) := by exact_mod_cast h24
          nlinarith
        constructor
        · omega
        · omega
      · -- Assume 5 ≤ n ∧ n ≤ 24, prove ⌊Real.logb 5 n⌋ = 1
        rintro ⟨h50, h24⟩
        have h51 : 5 ≤ n := by linarith
        have h52 : n ≤ 24 := by linarith
        have h10 : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h51
        have h11 : (n : ℝ) ≤ (24 : ℝ) := by exact_mod_cast h52
        have h14 : 1 ≤ Real.logb 5 (n : ℝ) := by
          have h15 : Real.logb 5 (5 : ℝ) = 1 := by
            rw [Real.logb_self_eq_one]
            all_goals norm_num
          have h16 : Real.logb 5 (5 : ℝ) ≤ Real.logb 5 (n : ℝ) := by
            apply Real.logb_le_logb_of_le
            all_goals
            try { norm_num  }
            all_goals
            try {  nlinarith  }
          nlinarith
        have h18 : Real.logb 5 (n : ℝ) < (2 : ℝ) := by
          have h18 : Real.logb 5 (n : ℝ) ≤ Real.logb 5 (24 : ℝ) := by
            apply Real.logb_le_logb_of_le
            all_goals
            try { norm_num  }
            all_goals
            try {  nlinarith  }
          have h107 : Real.logb 5 (24 : ℝ) < (2 : ℝ) := by
            have h107 : Real.logb 5 (24 : ℝ) < (2 : ℝ) := by
              have h121 : Real.logb 5 (25 : ℝ) = (2 : ℝ) := by
                calc
                  Real.logb 5 (25 : ℝ) = Real.logb 5 ((5) ^ 2) := by norm_num
                  _ = 2 := by simp [Real.logb_pow]
              have h7 : Real.logb 5 (24 : ℝ) < Real.logb 5 (25 : ℝ) := by
                apply Real.logb_lt_logb
                all_goals
                try { norm_num  }
                all_goals
                try {  nlinarith  }
              nlinarith
            linarith
          nlinarith
        have h90 : ⌊Real.logb 5 (n : ℝ)⌋ = 1 := by
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num) <;> try nlinarith
        exact_mod_cast h90
    · -- If n ≤ 0, contradiction
      have h2 : n = 0 := by omega
      rw [h2] 
      norm_num 
  rw [h1] 
  rw [finsum_mem_eq_toFinset_sum]
  simp [Set.toFinset, Set.Icc]
  all_goals try native_decide