import Mathlib

theorem algebra_165620 (u : ℝ) (hu : u ≠ 2) :
    u^2 / (2 - u^2) + u / (2 - u) = 2 ↔
    u = 1 ∨ u = (1 + Real.sqrt 33) / 4 ∨ u = (1 - Real.sqrt 33) / 4 := by
  constructor
  · -- Assume the equation holds, prove the roots
    intro h
    have h1 : 2 - u^2 ≠ 0 := by
      by_contra h1
      have h2 : u^2 / (2 - u^2) = 0 := by
        rw [h1]
        norm_num
      have h4 : u / (2 - u) = 2 := by
        linarith [h, h2]
      have h5 : u = 4 / 3 := by 
        field_simp [(show 2 - u ≠ 0 by
          intro h7
          apply hu
          linarith
        )] at h4 ⊢
        linarith
      have h6 : u^2 = 2 := by
        have h7 : 2 - u^2 = 0 := h1
        nlinarith
      rw [show u = 4 / 3 by linarith [h5]] at h6
      norm_num at h6
    have h2 : 2 - u ≠ 0 := by
      intro h3
      apply hu
      linarith
    have h3 : u^2 * (2 - u) + u * (2 - u^2) - 2 * (2 - u^2) * (2 - u) = 0 := by
      have h4 : u^2 / (2 - u^2) + u / (2 - u) = 2 := h
      have eq1 : u^2 / (2 - u^2) + u / (2 - u) - 2 = 0 := by linarith
      have eq2 : (u^2 * (2 - u) + u * (2 - u^2) - 2 * (2 - u^2) * (2 - u)) = 0 := by
        have eq3 : u^2 / (2 - u^2) + u / (2 - u) - 2 = (u^2 * (2 - u) + u * (2 - u^2) - 2 * (2 - u^2) * (2 - u)) / ((2 - u^2) * (2 - u)) := by
          field_simp [h1, h2]
          <;> ring
        rw [eq3] at eq1
        have h5 : (2 - u^2) * (2 - u) ≠ 0 := by
          apply mul_ne_zero
          exact h1
          exact h2
        field_simp at eq1 ⊢
        all_goals
          nlinarith
      linarith
    have h4 : -4 * u^3 + 6 * u^2 + 6 * u - 8 = 0 := by
      nlinarith [h3]
    have h5 : 4 * u^3 - 6 * u^2 - 6 * u + 8 = 0 := by
      linarith [h4]
    have h6 : (u - 1) * (4 * u^2 - 2 * u - 8) = 0 := by
      nlinarith [h5]
    cases' (mul_eq_zero.1 h6) with h7 h8
    · -- Case u - 1 = 0, so u = 1
      left
      linarith
    · -- Case 4u^2 - 2u - 8 = 0
      have h10 : 4 * u^2 - 2 * u - 8 = 0 := by
        linarith
      have h11 : 2 * u^2 - u - 4 = 0 := by
        nlinarith
      have h12 : (u - (1 + Real.sqrt 33) / 4) * (u - (1 - Real.sqrt 33) / 4) = 0 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
      cases' (mul_eq_zero.1 h12) with h13 h14
      · -- First root
        right
        left
        linarith
      · -- Second root
        right
        right
        linarith
  · -- Assume u is one of the roots, prove the equation
    rintro (h | h | h)
    · -- Case u = 1
      rw [h]
      norm_num
    · -- Case u = (1 + Real.sqrt 33) / 4
      rw [h]
      have h100 : ((1 + Real.sqrt 33) / 4 : ℝ) ^ 2 = (17 + Real.sqrt 33) / 8 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
      have h101 : (2 - ((1 + Real.sqrt 33) / 4 : ℝ) ^ 2 : ℝ) = ( -1 - Real.sqrt 33 ) / 8 := by 
        nlinarith [h100]
      have h102 : (2 - ((1 + Real.sqrt 33) / 4 : ℝ) ) = (7 - Real.sqrt 33) / 4 := by
        linarith
      have h107 : ((1 + Real.sqrt 33) / 4 : ℝ) ^ 2 / (2 - ((1 + Real.sqrt 33) / 4) ^ 2 ) + ((1 + Real.sqrt 33) / 4 : ℝ) / (2 - ((1 + Real.sqrt 33) / 4 : ℝ) ) = 2 := by
        rw [h101, h102, h100]
        field_simp [show -1 - Real.sqrt 33 ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        , show 7 - Real.sqrt 33 ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        ]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
      linarith [h107]
    · -- Case u = (1 - Real.sqrt 33) / 4
      rw [h]
      have h100 : ((1 - Real.sqrt 33) / 4 : ℝ) ^ 2 = (17 - Real.sqrt 33) / 8 := by
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
      have h101 : (2 - ((1 - Real.sqrt 33) / 4 : ℝ) ^ 2 : ℝ) = ( -1 + Real.sqrt 33 ) / 8 := by 
        nlinarith [h100]
      have h102 : (2 - ((1 - Real.sqrt 33) / 4 : ℝ) ) = (7 + Real.sqrt 33) / 4 := by
        linarith
      have h107 : ((1 - Real.sqrt 33) / 4 : ℝ) ^ 2 / (2 - ((1 - Real.sqrt 33) / 4) ^ 2 ) + ((1 - Real.sqrt 33) / 4 : ℝ) / (2 - ((1 - Real.sqrt 33) / 4 : ℝ) ) = 2 := by
        rw [h101, h102, h100]
        field_simp [show -1 + Real.sqrt 33 ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        , show 7 + Real.sqrt 33 ≠ 0 by 
          nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
        ]
        nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < (33 : ℝ) by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (33 : ℝ) by norm_num)]
      linarith [h107]