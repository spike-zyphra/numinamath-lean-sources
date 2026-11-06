import Mathlib

theorem algebra_134757 (x y : ℝ) :
    x^4 + x^2 * y^2 + y^4 = 481 ∧ x^2 + x * y + y^2 = 37 ↔
    (x = 4 ∧ y = 3) ∨ (x = 3 ∧ y = 4) ∨ (x = -3 ∧ y = -4) ∨ (x = -4 ∧ y = -3) := by
  constructor
  · -- Forward implication: if both equations hold, then one of the four solutions holds
    intro ⟨h₁, h₂⟩
    have h3 : (x^2 + x * y + y^2) * (x^2 - x * y + y^2) = 481 := by
      nlinarith [sq_nonneg (x^2 - y^2), sq_nonneg (x * y)]
    rw [h₂] at h3
    have h4 : x^2 - x * y + y^2 = 13 := by
      nlinarith
    have h5 : x * y = 12 := by
      nlinarith [sq_nonneg (x - y)]
    have h6 : (x + y)^2 = 49 := by
      nlinarith [sq_nonneg (x - y), h5]
    have h8 : x + y = 7 ∨ x + y = -7 := by
      have h9 : (x + y)^2 - 49 = 0 := by linarith
      have h10 : (x + y - 7) * (x + y + 7) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h10) with h11 h12
      · -- h11 is x + y - 7 = 0
        left
        linarith
      · -- h12 is x + y + 7 = 0
        right
        linarith
    cases h8 with
    | inl hxy =>
      have h7 : x + y = 7 := by linarith
      have h9 : x^2 - 7 * x + 12 = 0 := by
        have h9_1 : x + y = 7 := by linarith
        have h9_2 : x * y = 12 := h5
        have h9_3 : y = 7 - x := by linarith
        rw [h9_3] at h9_2
        nlinarith
      have h9f : (x - 3) * (x - 4) = 0 := by
        nlinarith [sq_nonneg (x - 3), sq_nonneg (x - 4), h9]
      cases' (mul_eq_zero.1 h9f) with hx3 hx4
      · -- x = 3
        have hx : x = 3 := by linarith
        have hy : y = 4 := by 
          nlinarith [hxy]
        simp [hx, hy]
      · -- x = 4
        have hx : x = 4 := by linarith
        have hy : y = 3 := by 
          nlinarith [hxy]
        simp [hx, hy]
    | inr hxy =>
      have h7 : x + y = -7 := by linarith
      have h9 : x^2 + 7 * x + 12 = 0 := by
        have h9_1 : x + y = -7 := by linarith
        have h9_2 : x * y = 12 := h5
        have h9_3 : y = -7 - x := by linarith
        rw [h9_3] at h9_2
        nlinarith
      have h9f : (x + 3) * (x + 4) = 0 := by
        nlinarith [sq_nonneg (x + 3), sq_nonneg (x + 4), h9]
      cases' (mul_eq_zero.1 h9f) with hx3 hx4
      · -- x = -3
        have hx : x = -3 := by linarith
        have hy : y = -4 := by 
          nlinarith [hxy]
        simp [hx, hy]
      · -- x = -4
        have hx : x = -4 := by linarith
        have hy : y = -3 := by 
          nlinarith [hxy]
        simp [hx, hy]
  · -- Backward direction: each of the four solutions satisfies both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (4, 3)
      constructor
      norm_num
      norm_num
    · -- (3, 4)
      constructor
      norm_num
      norm_num
    · -- (-3, -4)
      constructor
      norm_num
      norm_num
    · -- (-4, -3)
      constructor
      norm_num
      norm_num