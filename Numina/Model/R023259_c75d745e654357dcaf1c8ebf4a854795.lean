import Mathlib

theorem algebra_166159 {x y : ℝ} (h1 : (x + y) ^ 2 + 2 * x = 35 - 2 * y) (h2 : (x - y) ^ 2 - 2 * y = 3 - 2 * x) :
    (x, y) = (-5, -2) ∨ (x, y) = (3, 2) ∨ (x, y) = (-3, -4) ∨ (x, y) = (1, 4) := by
  have eq1 : x ^ 2 + y ^ 2 + 2 * x = 19 := by
    nlinarith [h1, h2]
  have eq2 : y * (x + 1) = 8 := by 
    nlinarith [h1, h2]
  have h4 : ((x + 1) ^ 2) ^ 2 - 20 * ((x + 1) ^ 2) + 64 = 0 := by
    nlinarith [eq1, eq2]
  have h5 : ((x + 1) ^ 2 - 16) * ((x + 1) ^ 2 - 4) = 0 := by
    nlinarith [h4]
  cases' (mul_eq_zero.1 h5) with h6 h7
  · -- Case where (x + 1) ^ 2 - 16 = 0, so (x + 1) ^ 2 = 16
    have h8 : (x + 1) ^ 2 = 16 := by 
      linarith
    have h9 : x + 1 = 4 ∨ x + 1 = -4 := by
      have h : (x + 1) ^ 2 = 16 := h8
      have h9 : (x + 1) ^ 2 - 16 = 0 := by linarith
      have h10 : (x + 1 - 4) * (x + 1 + 4) = 0 := by
        nlinarith
      cases' (mul_eq_zero.1 h10) with h11 h12
      · -- Case where x + 1 - 4 = 0, so x + 1 = 4
        left
        linarith
      · -- Case where x + 1 + 4 = 0, so x + 1 = -4
        right
        nlinarith
    cases' h9 with h10 h11
    · -- Case where x + 1 = 4, so x = 3
      have h12 : x = 3 := by
        nlinarith
      have h13 : y = 2 := by
        rw [show x + 1 = 4 by nlinarith [h12] ] at eq2
        nlinarith
      right
      left
      simp [h12, h13]
    · -- Case where x + 1 = -4, so x = -5
      have h14 : x = -5 := by
        nlinarith
      have h15 : y = -2 := by
        rw [show x + 1 = -4 by nlinarith [h14] ] at eq2
        nlinarith
      left
      simp [h14, h15]
  · -- Case where (x + 1) ^ 2 - 4 = 0, so (x + 1) ^ 2 = 4
    have h16 : (x + 1) ^ 2 = 4 := by 
      linarith
    have h9 : x + 1 = 2 ∨ x + 1 = -2 := by 
      have h8 : (x + 1) ^ 2 = 4 := h16
      have h9 : (x + 1) ^ 2 - 4 = 0 := by
        nlinarith
      have h10 : (x + 1 - 2) * (x + 1 + 2) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.1 h10) with h11 h12
      · -- Case where x + 1 - 2 = 0, so x + 1 = 2
        left
        linarith
      · -- Case where x + 1 + 2 = 0, so x + 1 = -2
        right
        nlinarith
    cases' h9 with h9 h9
    · -- Case where x + 1 = 2, so x = 1
      have h12 : x = 1 := by
        nlinarith
      have h13 : y = 4 := by
        rw [show x + 1 = 2 by nlinarith [h12] ] at eq2
        nlinarith
      right
      right
      right
      simp [h12, h13]
    · -- Case where x + 1 = -2, so x = -3
      have h14 : x = -3 := by
        nlinarith
      have h15 : y = -4 := by
        rw [show x + 1 = -2 by nlinarith [h14] ] at eq2
        nlinarith
      right
      right
      left
      simp [h14, h15]