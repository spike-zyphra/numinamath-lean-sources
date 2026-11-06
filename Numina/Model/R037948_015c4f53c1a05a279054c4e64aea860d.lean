import Mathlib

theorem number_theory_166744 (a : ℕ → ℤ)
    (h₀ : a 1 = 1)
    (h₁ : ∀ n, a (n + 1) = a n + ⌊Real.sqrt (a n)⌋) :
    ∀ N, ∃ m, m > N ∧ ∃ k, a m = k ^ 2 := by 
  have h₂ := h₁ 0 
  rw [h₀] at h₂ 
  exfalso 
  have eq1 := h₂ 
  by_cases h4 : a 0 ≥ 0 
  · -- Assume a 0 ≥ 0 
    by_cases h5 : a 0 ≤ 2 
    · -- Assume a 0 ≤ 2 
      have h6 : a 0 ≤ 2 := by 
        omega 
      have h7 : a 0 ≥ 0 := by 
        omega 
      have h8 : a 0 = 0 ∨ a 0 = 1 ∨ a 0 = 2 := by 
        omega 
      rcases h8 with (h8 | h8 | h8)
      · -- a 0 = 0 
        rw [show a 0 = 0 by linarith [h8] ] at eq1 
        norm_num [Int.floor_eq_iff] at eq1 
      · -- a 0 = 1 
        rw [show a 0 = 1 by linarith [h8] ] at eq1 
        norm_num [Int.floor_eq_iff] at eq1 
      · -- a 0 = 2 
        rw [show a 0 = 2 by linarith [h8] ] at eq1 
        have h91 : ⌊Real.sqrt ( (2 : ℤ) : ℝ )⌋ = (1 : ℤ) := by
          rw [Int.floor_eq_iff]
          constructor <;> (try norm_num)
          all_goals
            nlinarith [Real.sqrt_nonneg ( (2 : ℝ) ), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
        rw [h91] at eq1 
        norm_num [Int.floor_eq_iff] at eq1 
    · -- Assume a 0 > 2 
      have h8 : a 0 > 2 := by 
        by_contra h 
        push_neg at h 
        have h9 : a 0 ≤ 2 := by 
          omega 
        omega 
      have h9 : ⌊Real.sqrt ( (a 0 : ℤ) : ℝ )⌋ ≥ 1 := by 
        have h66 : (a 0 : ℝ) ≥ 1 := by exact_mod_cast (show a 0 ≥ 1 from by omega )
        have h67 : Real.sqrt ( (a 0 : ℝ) ) ≥ Real.sqrt ( (1 : ℝ) ) := Real.sqrt_le_sqrt (show (a 0 : ℝ) ≥ (1 : ℝ) by exact_mod_cast (show a 0 ≥ 1 by omega ) )
        have h68 : Real.sqrt ( (1 : ℝ) ) = 1 := Real.sqrt_one 
        have h69 : Real.sqrt ( (a 0 : ℝ) ) ≥ 1 := by linarith 
        by_contra h 
        push_neg at h 
        have h70 : ⌊Real.sqrt ( (a 0 : ℝ) )⌋ ≤ 0 := by 
          omega 
        have h71 : (⌊Real.sqrt ( (a 0 : ℝ) )⌋ : ℝ) ≤ 0 := by 
          exact_mod_cast h70 
        have h72 : Real.sqrt ( (a 0 : ℝ) ) < (1 : ℝ) := by 
          have h19 : Real.sqrt ( (a 0 : ℝ) ) < (⌊Real.sqrt ( (a 0 : ℝ) )⌋ + 1 : ℝ) := by 
              exact Int.lt_floor_add_one (Real.sqrt ( (a 0 : ℝ) )) 
          nlinarith 
        linarith 
      omega 
  · -- Assume a 0 < 0 
    have h6 : a 0 < 0 := by omega 
    have h7 : (a 0 : ℝ) < 0 := by exact_mod_cast h6 
    have h8 : Real.sqrt ( (a 0 : ℝ) ) = 0 := by 
      rw [Real.sqrt_eq_zero'.mpr (by nlinarith )] 
    norm_num [h8] at eq1 
    all_goals 
      omega