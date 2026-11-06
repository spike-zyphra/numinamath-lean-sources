import Mathlib

theorem calculus_15874
    (a b c : ℝ × ℝ × ℝ)
    (h₀ : a • b = -3)
    (h₁ : a • c = 4)
    (h₂ : b • c = 6) :
    b • (7 * c - 2 * a) = 48 := by
  have eq1 : b • (7 * c - 2 * a) = 7 * (b • c) - 2 * (a • b) := by
    simp [sub_eq_add_neg, dotProduct, Finset.sum, mul_add, mul_sub]
    <;> ring
  rw [eq1, h₀, h₂]
  all_goals norm_num