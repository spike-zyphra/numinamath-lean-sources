import Mathlib

theorem algebra_234344 (x y : ℤ) :
    y^2 * (y - x + 2) - y * (x + 4) + 5 * x + 7 = 0 ↔
    (x, y) = (15, 2) ∨ (x, y) = (10, -3) ∨ (x, y) = (-2, 1) ∨ (x, y) = (-5, -2) := by
  constructor
  · -- Forward implication: if the equation holds, prove the disjunction
    rintro h 
    have h1 : (y ^ 2 + y - 5) * (x - y - 1) = 12 := by 
      nlinarith 
    -- Let k be y^2 + y -5, so k divides 12
    have h5 : y = 2 ∨ y = -3 ∨ y = 1 ∨ y = -2 := by 
      have h6 : (y ^ 2 + y - 5) ∣ 12 := by 
        use x - y - 1 
        all_goals 
          linarith [h1] 
      have h7 : (y ^ 2 + y - 5) ≤ 12 := by 
        apply Int.le_of_dvd (by norm_num) h6 
      have h8 : (y ^ 2 + y - 5) ≥ -12 := by 
        have h9 : - (y ^ 2 + y - 5) ∣ 12 := by 
          exact Int.neg_dvd.2 h6 
        have h10 : - (y ^ 2 + y - 5) ≤ 12 := by 
          apply Int.le_of_dvd (by norm_num) h9 
        omega 
      have h9 : y ≤ 4 := by 
        by_contra h10
        push_neg at h10 
        have h10 : y ≥ 5 := by 
          omega 
        nlinarith [sq_nonneg (y : ℤ), sq_nonneg ((y + 1) : ℤ), sq_nonneg ((y - 2) : ℤ), sq_nonneg ((y + 3) : ℤ)]
      have h10 : y ≥ -4 := by 
        by_contra h11 
        push_neg at h11 
        have h11 : y ≤ -5 := by 
          omega 
        nlinarith [sq_nonneg (y : ℤ), sq_nonneg ((y + 1) : ℤ), sq_nonneg ((y - 2) : ℤ), sq_nonneg ((y + 3) : ℤ)]
      interval_cases y <;> norm_num at h6 h1 
      <;> try { tauto }
    rcases h5 with (rfl | rfl | rfl | rfl)
    · -- y = 2 
      have h100 : (2 ^ 2 + 2 - 5) * (x - 2 - 1) = 12 := by 
        simpa using h1 
      have hx : x = 15 := by 
        nlinarith 
      left 
      simp [hx]
    · -- y = -3 
      have h100 : ((-3) ^ 2 + (-3) - 5) * (x - (-3) - 1) = 12 := by 
        simpa using h1 
      have hx : x = 10 := by 
        nlinarith 
      right 
      left 
      simp [hx]
    · -- y = 1 
      have h100 : (1 ^ 2 + 1 - 5) * (x - 1 - 1) = 12 := by 
        simpa using h1 
      have hx : x = -2 := by 
        nlinarith 
      right 
      right 
      left 
      simp [hx]
    · -- y = -2 
      have h100 : ((-2) ^ 2 + (-2) - 5) * (x - (-2) - 1) = 12 := by 
        simpa using h1 
      have hx : x = -5 := by 
        nlinarith 
      right 
      right 
      right 
      simp [hx]
  · -- Backward implication: if (x,y) is one of the four pairs, then it solves the equation 
    rintro (h | h | h | h)
    · -- (15, 2)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩
      all_goals 
        norm_num 
    · -- (10, -3)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals 
        norm_num 
    · -- (-2, 1)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals 
        norm_num 
    · -- (-5, -2)
      simp [Prod.ext_iff] at h ⊢ 
      rcases h with ⟨rfl, rfl⟩ 
      all_goals 
        norm_num