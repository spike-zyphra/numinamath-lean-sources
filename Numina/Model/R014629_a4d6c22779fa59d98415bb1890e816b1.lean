import Mathlib

theorem algebra_241961 (x y : ℝ) :
    2 * (x ^ 4 + 3 * x ^ 2 + 6) * (y ^ 4 - 5 * y ^ 2 + 12) = 69 ↔
    (x = 0 ∧ y = Real.sqrt (5 / 2)) ∨ (x = 0 ∧ y = -Real.sqrt (5 / 2)) := by
  constructor
  · -- Forward, if equation then solutions.
    intro h
    have h1 : (x ^ 4 + 3 * x ^ 2 + 6) * (y ^ 4 - 5 * y ^ 2 + 12) = 34.5 := by
      nlinarith
    have h2 : x ^ 4 + 3 * x ^ 2 + 6 ≥ 6 := by
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg (x)]
    have h3 : y ^ 4 - 5 * y ^ 2 + 12 ≥ 23 / 4 := by
      nlinarith [sq_nonneg (y ^ 2 - 5 / 2), sq_nonneg (y)]
    have h5 : (x ^ 4 + 3 * x ^ 2 + 6) = 6 := by
      nlinarith [h1, h2, h3, sq_nonneg ((x ^ 4 + 3 * x ^ 2 + 6) - 6), sq_nonneg ((y ^ 4 - 5 * y ^ 2 + 12) - 23 / 4)]
    have hx : x = 0 := by
      have h6 : x ^ 4 + 3 * x ^ 2 = 0 := by
        nlinarith [h5]
      have h7 : x ^ 2 * (x ^ 2 + 3) = 0 := by
        nlinarith [h6]
      cases' (mul_eq_zero.1 h7) with h8 h9
      · -- x ^ 2 = 0
        have : x ^ 2 = 0 := by linarith
        have : x = 0 := by
          simp at this ⊢
          exact_mod_cast this
        linarith
      · -- x ^ 2 + 3 = 0
        nlinarith [sq_nonneg x]
    have h5' : y ^ 4 - 5 * y ^ 2 + 12 = 23 / 4 := by 
      rw [show x = 0 by linarith [hx]] at h1 
      nlinarith
    have h6 : (y ^ 2 - 5 / 2) ^ 2 = 0 := by 
      nlinarith [h5']
    have h7 : y ^ 2 = 5 / 2 := by 
      nlinarith [pow_eq_zero h6]
    have h8 : y = Real.sqrt (5 / 2) ∨ y = -Real.sqrt (5 / 2) := by 
      have h9 : y ^ 2 = 5 / 2 := h7 
      have h10 : y ^ 2 - (5 / 2) = 0 := by 
        linarith [h9] 
      have h11 : y = Real.sqrt (5 / 2) ∨ y = -Real.sqrt (5 / 2) := by 
        have h12 : y ^ 2 = (Real.sqrt (5 / 2)) ^ 2 := by 
          rw [h9] 
          have hh : (Real.sqrt (5 / 2)) ^ 2 = 5 / 2 := Real.sq_sqrt (by norm_num) 
          rw [hh] 
        have h13 : y ^ 2 = (Real.sqrt (5 / 2)) ^ 2 := h12 
        have h14 : y = Real.sqrt (5 / 2) ∨ y = -Real.sqrt (5 / 2) := by 
          have h15 : y ^ 2 = (Real.sqrt (5 / 2)) ^ 2 := h13 
          have h16 : y = Real.sqrt (5 / 2) ∨ y = -Real.sqrt (5 / 2) := by 
            rw [sq_eq_sq_iff_eq_or_eq_neg] at h15 
            all_goals 
              tauto 
          tauto 
        tauto 
      exact_mod_cast h11 
    cases h8 with
    | inl hy1 => 
      left 
      constructor 
      · exact hx 
      · exact hy1 
    | inr hy2 => 
      right 
      constructor 
      · exact hx 
      · exact hy2 
  · -- Backward, solutions imply equation
    rintro (h | h)
    · -- First solution
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      have h1 : (Real.sqrt (5 / 2) ) ^ 2 = 5 / 2 := by 
        rw [Real.sq_sqrt] 
        all_goals norm_num 
      have h2 : (Real.sqrt (5 / 2) ) ^ 4 = (5 / 2) ^ 2 := by 
        calc 
          (Real.sqrt (5 / 2) ) ^ 4 = ((Real.sqrt (5 / 2) ) ^ 2) ^ 2 := by ring 
          _ = (5 / 2) ^ 2 := by rw [h1] 
      have h3 : (Real.sqrt (5 / 2) ) ^ 4 - 5 * (Real.sqrt (5 / 2) ) ^ 2 + 12 = 23 / 4 := by 
        nlinarith [h1, h2] 
      norm_num at h3 ⊢ 
      all_goals nlinarith [h3, h1, h2, Real.sqrt_nonneg (5 / 2)]
    · -- Second solution 
      rcases h with ⟨hx, hy⟩ 
      rw [hx, hy]
      have h1 : (-Real.sqrt (5 / 2) ) ^ 2 = 5 / 2 := by 
        nlinarith [Real.sqrt_nonneg (5 / 2), Real.sq_sqrt (show (5 / 2 : ℝ) ≥ 0 by norm_num)]
      have h2 : (-Real.sqrt (5 / 2) ) ^ 4 = (5 / 2) ^ 2 := by 
        calc 
          (-Real.sqrt (5 / 2) ) ^ 4 = ((-Real.sqrt (5 / 2) ) ^ 2) ^ 2 := by ring 
          _ = (5 / 2) ^ 2 := by rw [h1] 
      have h3 : (-Real.sqrt (5 / 2) ) ^ 4 - 5 * (-Real.sqrt (5 / 2) ) ^ 2 + 12 = 23 / 4 := by 
        nlinarith [h1, h2] 
      norm_num at h3 ⊢ 
      all_goals nlinarith [h3, h1, h2, Real.sqrt_nonneg (5 / 2)]