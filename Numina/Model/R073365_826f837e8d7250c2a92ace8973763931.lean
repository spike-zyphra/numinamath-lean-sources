import Mathlib

theorem algebra_302812 {p q r : ℝ} (h₁ : r + q = 6 - 4 * p + 3 * p ^ 2) (h₂ : r - q = 5 - 4 * p + p ^ 2) :
    p < q ∧ q < r := by 
  have hr : r = (11 / 2) - 4 * p + 2 * p ^ 2 := by
    have h3 : 2 * r = 11 - 8 * p + 4 * p ^ 2 := by
      nlinarith [h₁, h₂]
    linarith
  have hq : q = (1 / 2) + p ^ 2 := by
    have h4 : 2 * q = 1 + 2 * p ^ 2 := by
      nlinarith [h₁, h₂]
    linarith
  -- Prove p < q
  have hpq : p < q := by
    rw [hq]
    nlinarith [sq_nonneg (p - 1 / 2)]
  -- Prove q < r
  have hqr : q < r := by
    rw [hq, hr]
    nlinarith [sq_nonneg (p - 2)]
  exact ⟨hpq, hqr⟩