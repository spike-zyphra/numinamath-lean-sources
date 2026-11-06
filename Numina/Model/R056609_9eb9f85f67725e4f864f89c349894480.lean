import Mathlib

theorem algebra_237851 (x y : ℝ) :
    x^2 - 2 * x * y = 1 ∧ 5 * x^2 - 2 * x * y + 2 * y^2 = 5 ↔
    (x = 1 ∧ y = 0) ∨ (x = -1 ∧ y = 0) ∨ (x = 1 / 3 ∧ y = -4 / 3) ∨ (x = -1 / 3 ∧ y = 4 / 3) := by 
  constructor
  · -- Forward direction: both equations hold implies the four solutions
    rintro ⟨h₁, h₂⟩
    
    have h₃ : 2 * x^2 + y^2 = 2 := by 
      nlinarith
  
    have h5 : (y) * (y + 4 * x) = 0 := by
      nlinarith [sq_nonneg (x * 3 - 1), sq_nonneg (x * 3 + 1), sq_nonneg (y + 4 * x), sq_nonneg (y - 0), sq_nonneg (x^2 - 1/9), sq_nonneg (x^2 - 1)]
  
    cases' (mul_eq_zero.mp h5) with hy1 hy2
  
    · -- Case 1: y = 0
      have h6 : x^2 = 1 := by 
        rw [hy1] at h₁
        nlinarith
  
      have hx1 : x = 1 ∨ x = -1 := by 
        rw [sq_eq_one_iff] at h6
        exact h6
  
      cases' hx1 with hx1 hx1
  
      · -- Subcase 1: x = 1, y = 0
        left 
        exact ⟨hx1, by linarith⟩ 
      · -- Subcase 2: x = -1, y = 0 
        right 
        left 
        exact ⟨hx1, by linarith⟩ 
    · -- Case 2: y + 4x = 0 
      have hy_eq : y = -4 * x := by 
        linarith
  
      have hx2 : x^2 = 1 / 9 := by 
        rw [hy_eq] at h₁ 
        nlinarith
  
      have hx3 : x = 1 / 3 ∨ x = -1 / 3 := by 
        have h1 : x^2 - (1/9) = 0 := by 
          linarith [hx2]
        have h2 : (x - 1/3) * (x + 1/3) = 0 := by 
          nlinarith
        cases' (mul_eq_zero.mp h2) with h3 h4
        · -- x - 1/3 = 0 => x = 1/3
          left 
          linarith 
        · -- x + 1/3 = 0 => x = -1/3 
          right 
          linarith 
      cases' hx3 with hx3 hx3
      · -- x = 1/3
        have hy3 : y = -4 / 3 := by 
          rw [hx3] at hy_eq 
          nlinarith 
        right 
        right 
        left 
        exact ⟨hx3, hy3⟩ 
      · -- x = -1/3 
        have hy3 : y = 4 / 3 := by 
          rw [hx3] at hy_eq 
          nlinarith 
        right 
        right 
        right 
        exact ⟨hx3, hy3⟩ 
  · -- Backward direction: the four solutions satisfy both equations 
    rintro (h | h | h | h)
    
    · -- (1, 0)
      rcases h with ⟨rfl, rfl⟩ 
      constructor
      · -- Equation 1
        norm_num 
      · -- Equation 2
        norm_num 
    · -- (-1, 0)
      rcases h with ⟨rfl, rfl⟩ 
      constructor
      · -- Equation 1
        norm_num 
      · -- Equation 2
        norm_num 
    · -- (1/3, -4/3)
      rcases h with ⟨rfl, rfl⟩ 
      constructor
      · -- Equation 1
        norm_num 
      · -- Equation 2
        norm_num 
    · -- (-1/3, 4/3)
      rcases h with ⟨rfl, rfl⟩ 
      constructor
      · -- Equation 1
        norm_num 
      · -- Equation 2
        norm_num