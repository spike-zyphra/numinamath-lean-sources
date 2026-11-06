import Mathlib

theorem algebra_14885 {h s : ℝ} (h₀ : h > 0) (h₁ : s > 0)
    (h₂ : (1 / 2) * s * h = s ^ 2) :
    h = 2 * s := by
  have eq1 : s * h = 2 * s ^ 2 := by
    nlinarith
  have eq2 : h = 2 * s := by
    apply (mul_left_inj' (ne_of_gt h₁)).mp
    linarith
  exact eq2