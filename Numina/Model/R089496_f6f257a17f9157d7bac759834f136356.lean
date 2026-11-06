import Mathlib

theorem algebra_95807 {x y : ℝ} (h₀ : x + y = 6) (h₁ : |x - y| = 8) :
    (x ^ 2 - 6 * x - 7 = 0 ∧ y ^ 2 - 6 * y - 7 = 0) := by
  cases eq_or_eq_neg_of_abs_eq h₁ with
  | inl h2 =>
    have hx : x = 7 := by
      linarith
    have hy : y = -1 := by
      rw [hx] at h₀
      linarith
    constructor
    · -- Show that x is a root: x^2 - 6x - 7 = 0
      rw [hx]
      norm_num
    · -- Show that y is a root: y^2 - 6 y - 7 = 0
      rw [hy]
      norm_num
  | inr h2 =>
    have hy : y = 7 := by
      linarith
    have hx : x = -1 := by
      rw [hy] at h₀
      linarith
    constructor
    · -- Show that x is a root: x^2 - 6 x - 7 = 0
      rw [hx]
      norm_num
    · -- Show that y is a root: y^2 - 6 y - 7 = 0
      rw [hy]
      norm_num