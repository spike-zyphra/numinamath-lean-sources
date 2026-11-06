import Mathlib

theorem algebra_284152 {A B : ℝ} {n c : ℝ} (h₀ : 0 < A) (h₁ : 0 < B)
    (h₂ : B > A) (h₃ : A * (1 + n / 100) = B) (h₄ : B * (1 - c / 100) = A) :
    A * Real.sqrt (100 + n) = B * Real.sqrt (100 - c) := by
  have h₅ : 0 < 100 + n := by
    nlinarith [h₀, h₁, h₃]
  have h₆ : 0 < 100 - c := by
    nlinarith [h₀, h₁, h₄]
  have h₇ : Real.sqrt (100 + n) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith [h₅]
  have h₈ : Real.sqrt (100 - c) > 0 := by
    apply Real.sqrt_pos.mpr
    linarith [h₆]

  have h₈ : (A * Real.sqrt (100 + n)) ^ 2 = (B * Real.sqrt (100 - c)) ^ 2 := by
    calc
      (A * Real.sqrt (100 + n)) ^ 2 = A ^ 2 * (Real.sqrt (100 + n) ^ 2) := by ring
      _ = A ^ 2 * (100 + n) := by
        rw [Real.sq_sqrt]
        nlinarith
      _ = B ^ 2 * (100 - c) := by 
        nlinarith [sq_nonneg (A * (n / 100) - B * (c / 100)), 
                  sq_nonneg (A - B * (1 - c / 100)), 
                  h₃, h₄, 
                  sq_pos_of_pos h₀, 
                  sq_pos_of_pos h₁, 
                  mul_pos h₀ (show 0 < A from h₀), 
                  mul_pos h₁ (show 0 < B from h₁), 
                  Real.sqrt_nonneg (100 + n), 
                  Real.sqrt_nonneg (100 - c)]
      _ = B ^ 2 * (Real.sqrt (100 - c) ^ 2) := by
        rw [Real.sq_sqrt]
        nlinarith
      _ = (B * Real.sqrt (100 - c)) ^ 2 := by ring

  have h₉ : A * Real.sqrt (100 + n) ≥ 0 := by 
    positivity
  have h₁₀ : B * Real.sqrt (100 - c) ≥ 0 := by 
    positivity
  have h₁₁ : A * Real.sqrt (100 + n) = B * Real.sqrt (100 - c) := by 
    nlinarith [Real.sqrt_nonneg (100 + n), Real.sqrt_nonneg (100 - c)]
  exact h₁₁