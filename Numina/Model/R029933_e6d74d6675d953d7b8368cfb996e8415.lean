import Mathlib

theorem algebra_327629 {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ∀ x : ℝ, (Real.sin x)^4 / a^2 + (Real.cos x)^4 / b^2 = 1 / (a^2 + b^2)) :
    ∀ x : ℝ, (Real.sin x)^100 / a^100 + (Real.cos x)^100 / b^100 = 2 / (a^2 + b^2)^50 := by

  have h1 := h 0
  have h2 : (Real.sin (0 : ℝ)) ^ 4 / a ^ 2 + (Real.cos (0 : ℝ)) ^ 4 / b ^ 2 = 1 / (a ^ 2 + b ^ 2) := by
    simpa using h1
  -- Simplify h2 using Real.sin_zero and Real.cos_zero.
  have h3 : Real.sin (0 : ℝ) = 0 := Real.sin_zero
  have h4 : Real.cos (0 : ℝ) = 1 := Real.cos_zero
  rw [h3, h4] at h2
  have eq1 : (0 : ℝ) ^ 4 / a ^ 2 + (1 : ℝ) ^ 4 / b ^ 2 = 1 / b^2 := by 
    field_simp
    <;> nlinarith
  have eq2 : 1 / b ^ 2 = 1 / (a ^ 2 + b ^ 2) := by
    linarith [h2, eq1]
  -- From eq2 derive a contradiction.
  have h3' : a ^ 2 = 0 := by 
    field_simp [(show b ^ 2 ≠ 0 by 
      exact pow_ne_zero 2 hb
    ), (show (a ^ 2 + b ^ 2) ≠ 0 by
        have hb2 : b^2 > (0 : ℝ) := by 
          exact sq_pos_of_ne_zero hb
        have ha2 : a^2 ≥ (0 : ℝ) := by 
          apply sq_nonneg 
        nlinarith
    )] at eq2 ⊢ 
    <;> nlinarith
  -- From h3' derive a=0, which contradicts ha: a ≠ 0
  have h4' : a = 0 := by 
    nlinarith
  -- Contradiction from ha and h4'
  contradiction