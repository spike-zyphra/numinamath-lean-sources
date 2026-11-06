import Mathlib

theorem algebra_120950 (a : ℝ) (ha : a ≠ 0) (x₁ x₂ : ℝ)
    (h₁ : a * x₁^2 - (a + 3) * x₁ + 2 = 0) (h₂ : a * x₂^2 - (a + 3) * x₂ + 2 = 0)
    (h₃ : x₁ * x₂ < 0) :
    a < 0 := by
  have h5 : a * x₁ * x₂ = 2 := by
    have eq1 : a * x₁^2 * x₂ - (a + 3) * x₁ * x₂ + 2 * x₂ = 0 := by
      have h₁' : a * x₁^2 - (a + 3) * x₁ + 2 = 0 := h₁
      have eq1 : (a * x₁^2 - (a + 3) * x₁ + 2) * x₂ = 0 := by
        rw [h₁']
        norm_num 
      linarith 
    have eq2 : a * x₂^2 * x₁ - (a + 3) * x₂ * x₁ + 2 * x₁ = 0 := by
      have h₂' : a * x₂^2 - (a + 3) * x₂ + 2 = 0 := h₂
      have eq2 : (a * x₂^2 - (a + 3) * x₂ + 2) * x₁ = 0 := by
        rw [h₂']
        norm_num 
      linarith
    have eq3 : (a * x₁^2 * x₂ - (a + 3) * x₁ * x₂ + 2 * x₂) - (a * x₂^2 * x₁ - (a + 3) * x₂ * x₁ + 2 * x₁) = (0 : ℝ) := by linarith [eq1, eq2]
    have eq4 : (a * x₁ * x₂ - 2) * (x₁ - x₂) = 0 := by
      nlinarith [eq3]
    cases' (mul_eq_zero.mp eq4) with h6 h7
    · -- Case where $a * x₁ * x₂ - 2 = 0$
      linarith 
    · -- Case where $x₁ - x₂ = 0$
      exfalso
      have h8 : x₁ = x₂ := by linarith 
      nlinarith [sq_pos_of_neg (show x₁ * x₂ < 0 by linarith), sq_nonneg (x₁ - x₂), h8]
  nlinarith [h₃, h5]