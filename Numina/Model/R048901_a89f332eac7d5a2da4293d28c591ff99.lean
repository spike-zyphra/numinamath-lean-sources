import Mathlib

theorem algebra_106216 {a b c d : ℝ}
    (h₀ : a * b + c + d = 3) (h₁ : b * c + d + a = 5) (h₂ : c * d + a + b = 2)
    (h₃ : d * a + b + c = 6) :
    a = 2 ∧ b = 0 ∧ c = 0 ∧ d = 3 := by
  have h4 : (a - 1) * (b - d) = -3 := by
    nlinarith
  have h5 : (c - 1) * (b - d) = 3 := by
    nlinarith
  have h6 : (1 - a) * (b - d) = 3 := by 
    nlinarith
  have h7 : (1 - a) * (b - d) = (c - 1) * (b - d) := by 
    linarith
  by_cases h8 : b - d = 0
  · -- contradiction from h8
    have h9 : (a - 1) * (b - d) = -3 := by linarith
    rw [h8] at h9
    nlinarith
  · -- Case $b - d ≠ 0$
    have h10 : 1 - a = c - 1 := by 
      apply (mul_left_inj' h8).mp
      linarith
    have h11 : c = 2 - a := by linarith
    have h12 : a = 2 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d - 3), 
        h₀, h₁, h₂, h₃]
    have h13 : b = 0 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d - 3), 
        h₀, h₁, h₂, h₃]
    have h14 : c = 0 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d - 3), 
        h₀, h₁, h₂, h₃]
    have h15 : d = 3 := by
      nlinarith [sq_nonneg (a - 2), sq_nonneg (b), sq_nonneg (c), sq_nonneg (d - 3), 
        h₀, h₁, h₂, h₃]
    exact ⟨h12, h13, h14, h15⟩