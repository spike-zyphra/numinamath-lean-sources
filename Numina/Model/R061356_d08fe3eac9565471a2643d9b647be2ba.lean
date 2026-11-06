import Mathlib

theorem algebra_96998 (k : ℝ) (h : k ≠ 0) :
    ¬∃ x : ℝ, x^2 + k * x + k^2 = 0 := by
  rintro ⟨x, hx⟩
  have h₁ : x^2 + k * x + k^2 = 0 := hx
  have h₂ : (x + k / 2)^2 = - (3 / 4) * k^2 := by
    nlinarith [sq_pos_of_ne_zero h]
  have h₃ : (x + k / 2) ^ 2 ≥ 0 := by
    apply sq_nonneg
  have h₄ : - (3 / 4) * k^2 ≤ 0 := by 
    nlinarith [sq_pos_of_ne_zero h]
  -- (x + k/2)^2 = - (3 / 4) * k^2
  -- ∴ (x + k/2)^2 ≤ 0
  have h₅ : (x + k / 2) ^ 2 = 0 := by 
    nlinarith [sq_nonneg k, h₂, h₃, h₄]
  have h₆ : k^2 = 0 := by
    nlinarith [sq_nonneg (x + k / 2), h₂, h₅, sq_pos_of_ne_zero h]
  have h₇ : k = 0 := by 
    rw [sq_eq_zero_iff] at h₆
    exact h₆
  contradiction