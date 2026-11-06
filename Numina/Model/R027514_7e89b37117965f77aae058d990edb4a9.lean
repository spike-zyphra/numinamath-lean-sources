import Mathlib

theorem algebra_188120 (x y : ℝ) (h₀ : x^2 + y = 13) (h₁ : x^6 + y^3 = 793) :
    (x = 3 ∧ y = 4) ∨ (x = -3 ∧ y = 4) ∨ (x = 2 ∧ y = 9) ∨ (x = -2 ∧ y = 9) := by
  have hy : y = 13 - x^2 := by linarith
  rw [hy] at h₁
  have h2 : x^4 - 13 * x^2 + 36 = 0 := by 
    nlinarith [sq_nonneg (x^2 - 4), sq_nonneg (x^2 - 9), sq_nonneg (x^2), sq_nonneg (x^2 - 4), sq_nonneg (x^2 - 9), sq_nonneg (x^2 * (x^2 - 4)), sq_nonneg (x^2 * (x^2 - 9)), sq_nonneg (x^2 - 4 * x^2), sq_nonneg (x^2 - 9 * x^2)]
  have h3 : (x^2 - 4) * (x^2 - 9) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case x^2 - 4 = 0, so x^2 = 4
    have h6 : x^2 = 4 := by linarith 
    have h7 : x = 2 ∨ x = -2 := by 
      have h8 : x^2 - 4 = 0 := by linarith 
      have h9 : (x - 2) * (x + 2) = 0 := by nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- x - 2 = 0, so x = 2 
        left
        linarith
      · -- x + 2 = 0, so x = -2 
        right
        linarith
    cases' h7 with h8 h9
    · -- x = 2 
      have h10 : y = 9 := by
        rw [h8] at hy
        nlinarith
      simp [h8, h10]
    · -- x = -2 
      have h10 : y = 9 := by 
        rw [h9] at hy
        nlinarith
      simp [h9, h10]
  · -- Case x^2 - 9 = 0, so x^2 = 9
    have h6 : x^2 = 9 := by linarith
    have h7 : x = 3 ∨ x = -3 := by
      have h8 : x^2 - 9 = 0 := by linarith
      have h9 : (x - 3) * (x + 3) = 0 := by 
        nlinarith
      cases' (mul_eq_zero.1 h9) with h10 h11
      · -- x - 3 = 0, so x = 3 
        left
        linarith
      · -- x + 3 = 0, so x = -3 
        right
        linarith
    cases' h7 with h8 h9
    · -- x = 3 
      have h10 : y = 4 := by 
        rw [h8] at hy
        nlinarith
      simp [h8, h10]
    · -- x = -3 
      have h10 : y = 4 := by 
        rw [h9] at hy
        nlinarith
      simp [h9, h10]