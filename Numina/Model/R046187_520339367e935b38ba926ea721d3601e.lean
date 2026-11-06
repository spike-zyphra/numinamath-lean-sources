import Mathlib

theorem algebra_94114 (a b : ℝ) :
Real.sqrt (a ^ 2 + b ^ 2) = a + b ↔ a * b = 0 ∧ a + b ≥ 0 := by
  constructor
  · -- Assume $\sqrt{a^2 + b^2} = a + b$, prove $a \cdot b = 0 \wedge a + b \geq 0$.
    intro h
    have h1 : a + b ≥ 0 := by
      by_contra h2
      push_neg at h2
      have h3 : Real.sqrt (a ^ 2 + b ^ 2) ≥ 0 := by positivity
      nlinarith [Real.sqrt_nonneg (a ^ 2 + b ^ 2), Real.sq_sqrt (show (0 : ℝ) ≤ a ^ 2 + b ^ 2 by nlinarith)]
    have h2 : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = (a + b) ^ 2 := by 
      rw [h]
    have h3 : (Real.sqrt (a ^ 2 + b ^ 2)) ^ 2 = a ^ 2 + b ^ 2 := by 
      rw [Real.sq_sqrt]
      positivity
    have h4 : a * b = 0 := by
      nlinarith 
    constructor
    · exact h4
    · exact h1
  · -- Assume $a \cdot b = 0 \wedge a + b \geq 0$, prove that $\sqrt{a^2 + b^2} = a + b$.
    rintro ⟨h1, h2⟩
    have h3 : (a + b) ^ 2 = a^2 + b^2 := by 
      nlinarith [h1]
    have h4 : Real.sqrt (a ^ 2 + b ^ 2) = Real.sqrt ((a + b) ^ 2) := by 
      have h6 : a ^ 2 + b ^ 2 = (a + b) ^ 2 := by linarith [h3]
      rw [h6]
    have h5 : Real.sqrt ((a + b) ^ 2) = a + b := by 
      rw [Real.sqrt_sq (by linarith)]
    rw [h4, h5]