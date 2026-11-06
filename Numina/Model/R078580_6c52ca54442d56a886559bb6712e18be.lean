import Mathlib

theorem algebra_146278 {f : ℝ → ℝ} (hf : ∀ x y, 2 * f x + 2 * f y - f x * f y ≥ 4) :
    ∀ x, f x = 2 := by
  have h1 : ∀ x, (f x - 2) ^ 2 ≤ 0 := by
    intro x
    have h := hf x x
    have h2 : (f x - 2) ^ 2 ≤ 0 := by
      nlinarith [sq_nonneg (f x - 2)]
    linarith
  intro x
  have h3 : (f x - 2) ^ 2 = 0 := by
    have h4 : (f x - 2) ^ 2 ≤ 0 := h1 x
    have h5 : (f x - 2) ^ 2 ≥ 0 := sq_nonneg (f x - 2)
    linarith
  have h4 : f x - 2 = 0 := by
    rw [sq_eq_zero_iff] at h3
    exact h3
  linarith