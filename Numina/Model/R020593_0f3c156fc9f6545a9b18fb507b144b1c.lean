import Mathlib

theorem algebra_300601 {a b : ℝ} (ha : 0 < a ∧ a < 1) (hb : 0 < b ∧ b < 1)
    (h1 : (7 + Real.sqrt 7) % 1 = a) (h2 : (7 - Real.sqrt 7) % 1 = b) :
    a * b - 3 * a + 2 * b + 1 = 0 := by

  have h3 : Real.sqrt 7 > 0 := by positivity
  have h4 : 2 < Real.sqrt 7 := by
    rw [Real.lt_sqrt] <;> norm_num
  have h5 : Real.sqrt 7 < 3 := by
    rw [Real.sqrt_lt] <;> norm_num

  have h6 : 9 < (7 + Real.sqrt 7 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]

  have h7 : (7 + Real.sqrt 7 : ℝ) < (10 : ℝ) := by
    nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 7 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]

  have h9 : ⌊(7 + Real.sqrt 7 : ℝ)⌋₊ = 9 := by 
    have h8 : ⌊(7 + Real.sqrt 7 : ℝ)⌋₊ = 9 := by 
      rw [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith
      all_goals 
        try tauto 
        all_goals 
          try { 
            have h81 : (9 : ℝ) ≤ (7 + Real.sqrt 7 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            have h82 : (7 + Real.sqrt 7 : ℝ) < (10 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            exact ⟨h81, by linarith⟩
          }
          all_goals 
            try tauto 
            all_goals 
              try nlinarith 
    exact h8

  have h10 : (7 + Real.sqrt 7 : ℝ) % 1 = Real.sqrt 7 - 2 := by
    have h100 : (7 + Real.sqrt 7 : ℝ) % 1 = (7 + Real.sqrt 7 - (9 : ℝ)) := by 
      have h90 : (7 + Real.sqrt 7 : ℝ) % 1 = (7 + Real.sqrt 7 - (↑(⌊(7 + Real.sqrt 7 : ℝ)⌋₊) : ℕ) : ℝ) := by 
        simp [Nat.floor_eq_iff]
        <;> ring_nf <;> norm_num at *
        all_goals 
          try linarith
          all_goals 
            try { 
              have h91 : (↑(⌊(7 + Real.sqrt 7 : ℝ)⌋₊) : ℝ) = (9 : ℝ) := by 
                exact_mod_cast h9 
              nlinarith 
            } 
            all_goals 
              try tauto 
              all_goals 
                try nlinarith 
      rw [h90]
      all_goals
        have h91 : (↑(⌊(7 + Real.sqrt 7 : ℝ)⌋₊) : ℝ) = (9 : ℝ) := by
          exact_mod_cast h9
        rw [h91]
        all_goals norm_num 
    have h110 : (7 + Real.sqrt 7 - (9 : ℝ) ) = (Real.sqrt 7 - (2 : ℝ) ) := by
      linarith
    rw [h110] at h100 
    all_goals linarith 
    all_goals norm_num

  have h8' : ⌊(7 - Real.sqrt 7 : ℝ)⌋₊ = 4 := by 
    have h91 : ⌊(7 - Real.sqrt 7 : ℝ)⌋₊ = 4 := by 
      rw [Nat.floor_eq_iff]
      constructor <;> (try norm_num) <;> try nlinarith 
      all_goals 
        try tauto 
        all_goals 
          try { 
            have h71 : (4 : ℝ) ≤ (7 - Real.sqrt 7 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            have h72 : (7 - Real.sqrt 7 : ℝ) < (5 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            exact ⟨h71, by linarith⟩
          }
          all_goals 
            try tauto 
            all_goals 
              try nlinarith 
    exact h91
  
  have h10' : (7 - Real.sqrt 7 : ℝ) % 1 = (3 - Real.sqrt 7 : ℝ) := by 
    have h101 : (7 - Real.sqrt 7 : ℝ) % 1 = (7 - Real.sqrt 7 - (4 : ℝ) ) := by 
      have h90 : (7 - Real.sqrt 7 : ℝ) % 1 = (7 - Real.sqrt 7 - (↑(⌊(7 - Real.sqrt 7 : ℝ)⌋₊) : ℕ) : ℝ) := by 
        simp [Nat.floor_eq_iff]
        <;> ring_nf <;> norm_num at *
        all_goals try linarith
        all_goals
          try { 
            have h71 : (4 : ℝ) ≤ (7 - Real.sqrt 7 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            have h72 : (7 - Real.sqrt 7 : ℝ) < (5 : ℝ) := by
              nlinarith [Real.sqrt_pos.mpr (show 0 < (7 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]
            have h91 : (↑(⌊(7 - Real.sqrt 7 : ℝ)⌋₊) : ℝ) = (4 : ℝ) := by
              exact_mod_cast h8'
            nlinarith [h91]
          }
          all_goals
            try tauto
            all_goals
              try nlinarith 
            all_goals
              norm_num
      rw [h90]
      all_goals
        have h91 : (↑(⌊(7 - Real.sqrt 7 : ℝ)⌋₊) : ℝ) = (4 : ℝ) := by
          exact_mod_cast h8'
        rw [h91]
        all_goals norm_num
    have h102 : ( (7 - Real.sqrt 7 - (4 : ℝ) ) = (3 - Real.sqrt 7 : ℝ) ) := by 
      nlinarith 
    rw [h102] at h101 
    all_goals linarith 
    all_goals norm_num
  
  -- Now we can find a and b
  have ha_eq : a = Real.sqrt 7 - 2 := by 
    linarith [h1, h10]
  
  have hb_eq : b = (3 - Real.sqrt 7 : ℝ) := by 
    linarith [h2, h10']

  rw [ha_eq, hb_eq]
  nlinarith [Real.sqrt_nonneg 7, Real.sq_sqrt (show (0 : ℝ) ≤ (7 : ℝ) by norm_num)]