import Mathlib

theorem algebra_134910 {x y z : ℝ} (h₀ : x ≠ y) (h₁ : y ≠ -2 * z) (h₂ : z ≠ 4 * x)
    (h₃ : 3 * x * y / (x - y) = 2) (h₄ : 2 * y * z / (y + 2 * z) = 3) (h₅ : x * z / (z - 4 * x) = 3) :
    x = -1 ∧ y = 2 ∧ z = -3 := by

  have eq1 : 3 * x * y = 2 * (x - y) := by
    have denom1 : x - y ≠ 0 := by
      intro h
      apply h₀
      linarith
    field_simp [denom1] at h₃ ⊢
    linarith

  have eq2 : 2 * y * z = 3 * (y + 2 * z) := by
    have denom2 : y + 2 * z ≠ 0 := by
      intro h
      apply h₁
      linarith
    field_simp [denom2] at h₄ ⊢
    linarith

  have eq3 : x * z = 3 * (z - 4 * x) := by
    have denom3 : z - 4 * x ≠ 0 := by
      intro h
      apply h₂
      linarith
    field_simp [denom3] at h₅ ⊢
    linarith
  
  have h1 : x = -1 := by
    nlinarith [sq_pos_of_ne_zero (show x - y ≠ 0 by intro h; apply h₀; linarith), sq_pos_of_ne_zero (show y + 2 * z ≠ 0 by intro h; apply h₁; linarith), sq_pos_of_ne_zero (show z - 4 * x ≠ 0 by intro h; apply h₂; linarith), sq_nonneg (x + 1), sq_nonneg (y - 2), sq_nonneg (z + 3)]
  
  have h2 : y = 2 := by
    rw [h1] at eq1
    nlinarith
  
  have h3 : z = -3 := by
    rw [h1] at eq3
    nlinarith
  
  exact ⟨h1, h2, h3⟩