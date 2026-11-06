import Mathlib

/- Let real numbers $a$, $b$, $c$ satisfy ${{a}^{2}}-bc-2a+10=0$, ${{b}^{2}}+bc+{{c}^{2}}-12a-15=0$, then the range of values for $a$ is ___          ___. -/
theorem algebra_10953 (a b c : ℝ) (h₀ : a^2 - b * c - 2 * a + 10 = 0) (h₁ : b^2 + b * c + c^2 - 12 * a - 15 = 0) :
    1 ≤ a ∧ a ≤ 5 := by

  have h2 : b * c = a^2 - 2 * a + 10 := by 
    linarith
  
  have h3 : b^2 + c^2 ≥ 2 * (b * c) := by 
    linarith [sq_nonneg (b - c)]
  
  have h4 : b^2 + b * c + c^2 ≥ 3 * (b * c) := by
    nlinarith [sq_nonneg (b - c)]

  have h5 : 12 * a + 15 ≥ 3 * (b * c) := by 
    nlinarith [h₁, h4]

  have h7 : a^2 - 6 * a + 5 ≤ 0 := by
    rw [show b * c = a^2 - 2 * a + 10 by linarith] at h5
    nlinarith
  
  constructor
  · -- Prove 1 ≤ a
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 5), h7]
  · -- Prove a ≤ 5
    nlinarith [sq_nonneg (a - 1), sq_nonneg (a - 5), h7]