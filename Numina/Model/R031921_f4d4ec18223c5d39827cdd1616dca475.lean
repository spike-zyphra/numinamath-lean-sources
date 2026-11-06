import Mathlib

theorem inequalities_321623 (a b : ℝ) :
    (∀ x y : ℝ, x^2 + 4 * x * y + 4 * y^2 + 10 * x + a * y + b > 0) ↔ a = 20 ∧ b > 25 := by
  constructor
  · -- Assume inequality holds for all x, y need to show a = 20 and b > 25
    intro h
    have h3 : ∀ y : ℝ, (a - 20) * y + b > 0 := by
      intro y
      specialize h (-2 * y) y
      have h4 : (-2 * y) ^ 2 + 4 * (-2 * y) * y + 4 * y ^ 2 + 10 * (-2 * y) + a * y + b = (a - 20) * y + b := by
        ring_nf
      linarith [h4, h]
    
    have h1 : a = 20 := by 
      by_cases h50 : a - 20 > 0
      · -- Assume a - 20 > 0
        have h4 : ∃ Y : ℝ, (a - 20) * Y + b ≤ (0 : ℝ) := by 
          use (- (b + 1) / (a - 20))
          have h6 : a - 20 > 0 := h50
          have : (a - 20) * (- (b + 1) / (a - 20)) + b ≤ (0 : ℝ) := by
            have h7 : a - 20 > 0 := h50
            have h7' : (a - 20) * (- (b + 1) / (a - 20)) = - (b + 1) := by
              field_simp [h6]
            nlinarith [h7']
          linarith
        rcases h4 with ⟨Y, h4⟩
        have h4' := h3 Y
        linarith
      by_cases h51 : a - 20 < (0 : ℝ)
      · -- Assume a - 20 < 0
        have h4 : ∃ Y : ℝ, (a - 20) * Y + b ≤ (0 : ℝ) := by
          use ( (-1 - b) / (a - 20) )
          have h6 : a - 20 < (0 : ℝ) := h51
          have : (a - 20) * ( (-1 - b) / (a - 20) ) + b ≤ (0 : ℝ) := by
            have h7 : a - 20 < (0 : ℝ) := h51
            have h7' : (a - 20) * ( (-1 - b) / (a - 20) ) = -1 - b := by
              field_simp [(show a - 20 ≠ 0 by linarith)]
            nlinarith [h7']
          linarith
        rcases h4 with ⟨Y, h4⟩
        have h4' := h3 Y
        linarith
      have h52 : a - 20 = 0 := by
        linarith
      linarith
    have h2 : b > 25 := by
      have h4 := h (-5) (0 : ℝ)
      norm_num [h1] at h4 ⊢
      linarith
    constructor
    · -- Show a = 20 
      linarith [h1]
    · -- Show b > 25
      linarith [h2]
  · -- Assume a = 20 ∧ b > 25, need to prove ∀ x y, expression > 0
    rintro ⟨ha, hb⟩
    intro x y
    have h1 : x^2 + 4 * x * y + 4 * y^2 + 10 * x + a * y + b > 0 := by
      rw [show a = 20 by linarith [ha]]
      nlinarith [sq_nonneg (x + 2 * y + 5), sq_nonneg (y), sq_nonneg (x + 2 * y), sq_nonneg (x + 4 * y), sq_nonneg (x - 2 * y), sq_nonneg (x + 2 * y - (-5)), sq_nonneg (x * (x + 2 * y)), sq_nonneg ((x + 2 * y) * y), sq_pos_of_pos (show (0 : ℝ) < 1 by norm_num)]
    linarith [h1]