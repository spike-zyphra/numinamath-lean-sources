import Mathlib

theorem algebra_298649 (a d : ℕ) (h₀ : a > 0) (h₁ : d > 0)
    (h₂ : a * (a + 3 * d) = (0.001 : ℝ) ^ (-a ^ 2 : ℝ)) (h₃ : (a + d) ^ 2 + (a + 2 * d) ^ 2 =
    5 * (Nat.choose 20 0)) :
    a = 1 ∧ d = 3 := by 
  have h4 : (a + d) ^ 2 + (a + 2 * d) ^ 2 = 5 := by 
    simp [Nat.choose] at h₃
    linarith
  have h5 : a ≥ 1 := by 
    linarith
  have h6 : d ≥ 1 := by 
    linarith
  have h7 : a + d ≥ 2 := by 
    linarith [h5, h6]
  have h8 : a + 2 * d ≥ 3 := by 
    linarith [h5, h6]
  have h9 : (a + d) ^ 2 ≥ 4 := by 
    nlinarith
  have h10 : (a + 2 * d) ^ 2 ≥ 9 := by 
    nlinarith
  nlinarith