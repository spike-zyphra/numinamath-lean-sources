import Mathlib

theorem algebra_123994 {p : ℝ} (h : ∃ x1 x2, x1^2 + p * x1 + 18 = 0 ∧ x2^2 + p * x2 + 18 = 0 ∧ x1 = 2 * x2) :
    p = 9 ∨ p = -9 := by 
  rcases h with ⟨x1, x2, h1, h2, h3⟩
  have eq1 : (2 * x2)^2 + p * (2 * x2) + 18 = 0 := by 
    rw [show x1 = 2 * x2 by linarith [h3]] at h1 
    linarith 
  have eq2 : x2^2 + p * x2 + 18 = 0 := h2 
  have eq3 : x2^2 = 9 := by
    nlinarith [sq_nonneg (x2), sq_nonneg (p)]
  have h4 : x2 = 3 ∨ x2 = -3 := by 
    have h5 : x2^2 - 9 = 0 := by linarith 
    have h6 : (x2 - 3) * (x2 + 3) = 0 := by 
      linarith 
    cases' (mul_eq_zero.mp h6) with h7 h8 
    · -- case where x2 - 3 = 0 
      left 
      linarith 
    · -- case where x2 + 3 = 0 
      right 
      linarith 
  cases' h4 with h5 h6 
  · -- case x2 = 3 
    have hp : p = -9 := by
      rw [h5] at h2 
      nlinarith 
    right 
    linarith 
  · -- case x2 = -3 
    have hp : p = 9 := by 
      rw [h6] at h2 
      nlinarith 
    left 
    linarith