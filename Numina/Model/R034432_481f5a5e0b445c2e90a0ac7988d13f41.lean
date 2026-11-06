import Mathlib

theorem algebra_122117 (x y : ℤ) : x - y = x^2 + x * y + y^2 ↔
    (x = 0 ∧ y = 0) ∨ (x = 1 ∧ y = 0) ∨ (x = 0 ∧ y = -1) ∨ (x = 2 ∧ y = -1) ∨
    (x = 1 ∧ y = -2) ∨ (x = 2 ∧ y = -2) := by
  constructor
  · -- Assume x - y = x ^ 2 + x * y + y ^ 2, prove the disjunction of the solutions
    intro h
    have h1 : y ≥ -2 := by 
      nlinarith [sq_nonneg (x + y + 1), sq_nonneg (x - 1), sq_nonneg (y + 1), sq_nonneg (x - y)]
    have h2 : y ≤ 0 := by 
      nlinarith [sq_nonneg (x + y + 1), sq_nonneg (x - 1), sq_nonneg (y + 1), sq_nonneg (x - y)]
    have h3 : y = 0 ∨ y = -1 ∨ y = -2 := by 
      omega 
    rcases h3 with h3 | h3 | h3
    · -- y = 0 
      have hy : y = 0 := h3
      rw [hy] at h
      have h4 : x = 0 ∨ x = 1 := by 
        have h_eq : x ^ 2 - x = 0 := by
          nlinarith 
        have h_eq2 : x * (x - 1) = 0 := by
          nlinarith 
        cases' (mul_eq_zero.1 h_eq2) with h5 h6
        · -- x = 0
          left 
          linarith 
        · -- x - 1 = 0 
          right 
          linarith 
      rcases h4 with h4 | h4
      · -- x = 0
        left 
        constructor
        · -- Show x = 0 
          linarith 
        · -- Show y = 0 
          linarith [h4] 
      · -- x = 1
        right 
        left 
        constructor 
        · -- Show x = 1 
          linarith 
        · -- Show y = 0 
          linarith 
    · -- y = -1
      have hy : y = -1 := h3
      rw [hy] at h
      have h4 : x = 0 ∨ x = 2 := by 
        have h_eq : x ^ 2 - 2 * x = 0 := by
          nlinarith 
        have h_eq2 : x * (x - 2) = 0 := by 
          linarith 
        cases' (mul_eq_zero.1 h_eq2) with h5 h6 
        · -- x = 0 
          left 
          linarith 
        · -- x - 2 = 0 
          right 
          linarith 
      rcases h4 with h4 | h4 
      · -- x = 0 
        right 
        right 
        left 
        constructor 
        · -- Show x = 0 
          linarith 
        · -- Show y = -1 
          linarith 
      · -- x = 2 
        right 
        right 
        right 
        left 
        constructor 
        · -- Show x = 2 
          linarith 
        · -- Show y = -1 
          linarith 
    · -- y = -2 
      have hy : y = -2 := h3
      rw [hy] at h 
      have h4 : x = 1 ∨ x = 2 := by 
        have h_eq : x ^ 2 - 3 * x + 2 = 0 := by 
          nlinarith 
        have h_eq2 : (x - 1) * (x - 2) = 0 := by 
          nlinarith 
        cases' (mul_eq_zero.1 h_eq2) with h5 h6 
        · -- x - 1 = 0 
          left 
          linarith 
        · -- x - 2 = 0 
          right 
          linarith 
      rcases h4 with h4 | h4 
      · -- x = 1 
        right 
        right 
        right 
        right 
        left 
        constructor 
        · -- Show x = 1 
          linarith 
        · -- Show y = -2 
          linarith 
      · -- x = 2 
        right 
        right 
        right 
        right 
        right 
        constructor 
        · -- Show x = 2 
          linarith 
        · -- Show y = -2 
          linarith 
  · -- Show that the solutions satisfy the equation 
    rintro (h | h | h | h | h | h)
    · -- (0, 0) 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (1, 0) 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (0, -1) 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (2, -1) 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (1, -2) 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num 
    · -- (2, -2) 
      rcases h with ⟨rfl, rfl⟩ 
      norm_num