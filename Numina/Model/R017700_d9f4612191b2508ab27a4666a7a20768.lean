import Mathlib

theorem algebra_6633 {a b c : ℝ} (h₀ : 1 / a + 1 / b + 1 / c = 1) (h₁ : a + b + c = 11)
    (h₂ : a ^ 2 + b ^ 2 + c ^ 2 = 49) :
    a ^ 3 + b ^ 3 + c ^ 3 = 251 := by
  have h3 : a * b + b * c + c * a = 36 := by 
    have h4 : (a + b + c) ^ 2 = a ^ 2 + b ^ 2 + c ^ 2 + 2 * (a * b + b * c + c * a) := by 
      ring
    rw [h₁, h₂] at h4 
    linarith 
  have h4 : a ≠ 0 := by
    by_contra h 
    have h5 : a = 0 := h 
    have eq1 : b + c = 11 := by 
      rw [h5] at h₁ 
      linarith 
    have eq2 : b ^ 2 + c ^ 2 = 49 := by 
      rw [h5] at h₂ 
      linarith 
    have eq3 : b * c = 36 := by 
      rw [h5] at h3 
      nlinarith 
    have h₄ : 1 / b + 1 / c = 1 := by 
      rw [h5] at h₀ 
      field_simp at h₀ ⊢ 
      all_goals try linarith 
    by_cases h5 : b = 0 
    · -- Assume b = 0 
      have h₆ : b = 0 := h5 
      rw [h₆] at eq3 
      nlinarith 
    · -- Assume b ≠ 0 
      by_cases h5' : c = 0 
      · -- Assume c = 0 
        have h₇ : c = 0 := h5' 
        rw [h₇] at eq3 
        nlinarith 
      · -- Assume c ≠ 0 
        have h₆ : b ≠ 0 := by 
          intro hb 
          have h₆ : b = 0 := by linarith 
          contradiction 
        have h₇ : c ≠ 0 := by 
          intro hc 
          have h₇ : c = 0 := by linarith 
          contradiction 
        field_simp at h₄ 
        nlinarith [sq_pos_of_ne_zero (show (b : ℝ ) ≠ 0 by
          intro hb 
          have h₆ : b = 0 := by linarith 
          contradiction 
        ), sq_pos_of_ne_zero (show (c : ℝ ) ≠ 0 by 
          intro hc 
          have h₇ : c = 0 := by linarith 
          contradiction 
        )
        ]
  -- similarly derive b ≠ 0, c ≠ 0 
  have h5 : b ≠ 0 := by 
    by_contra h 
    have h5 : b = 0 := h 
    have eq1 : a + c = 11 := by 
      rw [h5] at h₁ 
      linarith 
    have eq2 : a ^ 2 + c ^ 2 = 49 := by 
      rw [h5] at h₂ 
      linarith 
    have eq3' : a * c = 36 := by 
      rw [h5] at h3 
      nlinarith 
    have h₄ : 1 / a + 1 / c = 1 := by 
      rw [h5] at h₀ 
      field_simp at h₀ ⊢ 
      all_goals try linarith 
    by_cases h5 : a = 0 
    · -- Assume a = 0 
      have h₆ : a = 0 := h5 
      rw [h₆] at eq3' 
      nlinarith 
    · -- Assume a ≠ 0 
      by_cases h5' : c = 0 
      · -- Assume c = 0 
        have h₇ : c = 0 := h5' 
        rw [h₇] at eq3' 
        nlinarith 
      · -- Assume c ≠ 0 
        have h₆ : a ≠ 0 := by 
          intro ha 
          have h₆ : a = 0 := by linarith 
          contradiction 
        have h₇ : c ≠ 0 := by 
          intro hc 
          have h₇ : c = 0 := by linarith 
          contradiction 
        field_simp at h₄ 
        nlinarith [sq_pos_of_ne_zero (show (a : ℝ ) ≠ 0 by 
          intro ha 
          have h₆ : a = 0 := by linarith 
          contradiction 
        ), sq_pos_of_ne_zero (show (c : ℝ ) ≠ 0 by 
          intro hc 
          have h₇ : c = 0 := by linarith 
          contradiction 
        )
        ]
  -- derive c ≠ 0 
  have h6 : c ≠ 0 := by 
    by_contra h 
    have h6 : c = 0 := h 
    have eq1 : a + b = 11 := by 
      rw [h6] at h₁ 
      linarith 
    have eq2 : a ^ 2 + b ^ 2 = 49 := by 
      rw [h6] at h₂ 
      linarith 
    have eq3' : a * b = 36 := by 
      rw [h6] at h3 
      nlinarith 
    have h₄ : 1 / a + 1 / b = 1 := by 
      rw [h6] at h₀ 
      field_simp at h₀ ⊢ 
      all_goals try linarith 
    by_cases h5 : a = 0 
    · -- Assume a = 0 
      have h₆ : a = 0 := h5 
      rw [h₆] at eq3' 
      nlinarith 
    · -- Assume a ≠ 0 
      by_cases h5' : b = 0 
      · -- Assume b = 0 
        have h₇ : b = 0 := h5' 
        rw [h₇] at eq3' 
        nlinarith 
      · -- Assume b ≠ 0 
        have h₆ : a ≠ 0 := by 
          intro ha 
          have h₆ : a = 0 := by linarith 
          contradiction 
        have h₇ : b ≠ 0 := by 
          intro hb 
          have h₇ : b = 0 := by linarith 
          contradiction 
        field_simp at h₄ 
        nlinarith [sq_pos_of_ne_zero (show (a : ℝ ) ≠ 0 by 
          intro ha 
          have h₆ : a = 0 := by linarith 
          contradiction 
        ), sq_pos_of_ne_zero (show (b : ℝ ) ≠ 0 by 
          intro hb 
          have h₇ : b = 0 := by linarith 
          contradiction 
        )
        ]
  have h7 : a * b * c = 36 := by 
    field_simp [h4, h5, h6] at h₀ 
    nlinarith [h₀, h3]
  -- Use the identity to find a^3 + b^3 + c^3
  have h8 : a ^ 3 + b ^ 3 + c ^ 3 = (a + b + c) ^ 3 - 3 * (a + b + c) * (a * b + b * c + c * a) + 3 * (a * b * c) := by 
    ring 
  rw [h8, h₁, h3, h7]
  norm_num