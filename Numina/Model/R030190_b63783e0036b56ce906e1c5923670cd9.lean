import Mathlib

theorem algebra_303042 (x y : ℤ) : y^4 + 2 * x^4 + 1 = 4 * x^2 * y ↔ (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = 1) := by
  constructor
  · -- Assume y^4 + 2 * x^4 + 1 = 4 * x^2 * y, prove (x = 1 ∧ y = 1) ∨ (x = -1 ∧ y = 1)
    rintro h_eq
    have h2 : y^4 + 2 * x^4 + 1 = 4 * x^2 * y := h_eq 
    have h3 : 2 * (x^2 - y) ^ 2 + (y^2 - 1) ^ 2 = 0 := by 
      nlinarith [sq_nonneg (x^2 - y), sq_nonneg (y^2 - 1), sq_nonneg (x), sq_nonneg (y), sq_nonneg (y - 1), sq_nonneg (x^2 - 1)]
    have h4 : 2 * (x^2 - y) ^ 2 = 0 := by 
      nlinarith [show 2 * (x^2 - y) ^ 2 ≥ 0 by positivity, 
        show (y^2 - 1) ^ 2 ≥ 0 by positivity, h3]
    have h5 : (y^2 - 1) ^ 2 = 0 := by 
      nlinarith [show 2 * (x^2 - y) ^ 2 ≥ 0 by positivity, 
        show (y^2 - 1) ^ 2 ≥ 0 by positivity, h3]
    have h8 : y^2 = 1 := by 
      have h7 : y^2 - 1 = 0 := by
        nlinarith 
      nlinarith 
    have h9 : y = 1 ∨ y = -1 := by 
      rw [sq_eq_one_iff] at h8 
      exact h8 
    have h10 : x^2 - y = 0 := by 
      nlinarith 
    rcases h9 with (h11 | h12)
    · -- Case h11, so y = 1 
      have h13 : x^2 = 1 := by 
        have h14 : x^2 - y = 0 := by 
          nlinarith 
        rw [show y = 1 by linarith [h11] ] at h14 
        nlinarith 
      have h14 : x = 1 ∨ x = -1 := by 
        have h15 : x^2 = 1 := h13 
        rw [sq_eq_one_iff] at h15 
        exact h15 
      rcases h14 with (h15 | h16)
      · -- Case h15, so x = 1 and y=1 
        left 
        exact ⟨h15, h11⟩ 
      · -- Case h16, so x = -1 and y=1 
        right 
        exact ⟨h16, h11⟩ 
    · -- Case h12, so y = -1 
      have h14 : x^2 = -1 := by 
        have h15 : x^2 - y = 0 := by 
          nlinarith 
        rw [show y = -1 by linarith [h12] ] at h15 
        nlinarith 
      nlinarith [sq_nonneg (x)]
  · -- Reverse direction
    rintro (h | h)
    · -- Case h, so (x = 1 ∧ y = 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num
    · -- Case h, so (x = -1 ∧ y = 1)
      rcases h with ⟨hx, hy⟩
      rw [hx, hy]
      norm_num