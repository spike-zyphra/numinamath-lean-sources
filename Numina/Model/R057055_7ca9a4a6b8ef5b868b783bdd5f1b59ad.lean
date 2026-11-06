import Mathlib

theorem algebra_223465 {x y : ℝ} (hx : x ≠ y) (hy : y ≠ x) :
    x + 1 / (y - x) = 1 ∧ y + 1 / (x - y) = 2 ↔
    (x = 2 ∧ y = 1) ∨ (x = 1 / 2 ∧ y = 5 / 2) := by
  constructor
  · -- Assume the equations hold, and derive the possible solutions
    rintro ⟨h₁, h₂⟩
    have h3 : y - x ≠ 0 := by
      intro h
      apply hx
      linarith
    have h4 : x - y ≠ 0 := by
      intro h
      apply hy
      linarith
    have eq1 : x + 1 / (y - x) = 1 := h₁
    have eq2 : y + 1 / (x - y) = 2 := h₂
    have eq3 : x * (y - x) + 1 = y - x := by
      have h5 : y - x ≠ 0 := h3
      field_simp [h5] at eq1 ⊢
      linarith
    have eq4 : y * (x - y) + 1 = 2 * (x - y) := by
      have h6 : x - y ≠ 0 := by 
        intro h
        apply hy
        linarith
      field_simp [h6] at eq2 ⊢
      linarith
    have sq_eq : (y - x)^2 - (y - x) - 2 = 0 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (x - 1 / 2), sq_nonneg (y - 1), sq_nonneg (y - 5 / 2)]
    have factored : ((y - x) - 2) * ((y - x) + 1) = 0 := by 
      nlinarith [sq_eq]
    cases' (mul_eq_zero.mp factored) with h5 h6
    · -- Case where y - x = 2 
      have h7 : y - x = 2 := by linarith 
      have hx' : x = 1 / 2 := by 
        have eq5 : x * (y - x) + 1 = y - x := by nlinarith [eq3]
        rw [h7] at eq5 
        nlinarith 
      have hy' : y = 5 / 2 := by 
        linarith [hx']
      right 
      exact ⟨by linarith, by linarith⟩
    · -- Case where y - x = -1 
      have h7 : y - x = -1 := by linarith 
      have hx' : x = 2 := by 
        have eq5 : x * (y - x) + 1 = y - x := by nlinarith [eq3]
        rw [h7] at eq5 
        nlinarith 
      have hy' : y = 1 := by 
        linarith [hx']
      left 
      exact ⟨by linarith, by linarith⟩
  · -- Verify the two solutions satisfy both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · 
      constructor
      · norm_num 
      · norm_num
    · 
      constructor
      · norm_num 
      · norm_num