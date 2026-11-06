import Mathlib

open Real Set
open scoped Real

theorem algebra_161527 (α : ℝ) (h : sin α ≠ 0 ∧ cos α ≠ 0) :
    (sin α ^ 4 + cos α ^ 4 - 1) / (sin α ^ 6 + cos α ^ 6 - 1) = 2 / 3 := by
  have h1 : sin α ^ 2 + cos α ^ 2 = 1 := Real.sin_sq_add_cos_sq α
  have h2 : sin α ^ 4 + cos α ^ 4 = (sin α ^ 2 + cos α ^ 2) ^ 2 - 2 * (sin α ^ 2 * cos α ^ 2) := by
    ring
  have h3 : sin α ^ 4 + cos α ^ 4 = 1 - 2 * (sin α ^ 2 * cos α ^ 2) := by
    rw [h2, h1]
    all_goals linarith
  have h4 : sin α ^ 6 + cos α ^ 6 = (sin α ^ 2 + cos α ^ 2) ^ 3 - 3 * (sin α ^ 2 * cos α ^ 2) * (sin α ^ 2 + cos α ^ 2) := by
    ring_nf
  have h5 : sin α ^ 6 + cos α ^ 6 = 1 - 3 * (sin α ^ 2 * cos α ^ 2) := by
    rw [h4, h1]
    all_goals linarith
  have h6 : sin α ^ 4 + cos α ^ 4 - 1 = -2 * (sin α ^ 2 * cos α ^ 2) := by
    linarith [h3]
  have h7 : sin α ^ 6 + cos α ^ 6 - 1 = -3 * (sin α ^ 2 * cos α ^ 2) := by
    linarith [h5]
  -- $\sin \alpha \neq 0$ and $\cos \alpha \neq 0$ from hypothesis, so $\sin^2 \alpha \cos^2 \alpha \neq 0$
  have h8 : sin α ^ 2 * cos α ^ 2 ≠ 0 := by
    apply mul_ne_zero
    · -- $\sin^2 \alpha \neq 0$ since $\sin \alpha \neq 0$
      apply pow_ne_zero 2
      exact h.1
    · -- $\cos^2 \alpha \neq 0$ since $\cos \alpha \neq 0$
      apply pow_ne_zero 2
      exact h.2
  rw [show sin α ^ 4 + cos α ^ 4 - 1 = -2 * (sin α ^ 2 * cos α ^ 2) by linarith [h6]]
  rw [show sin α ^ 6 + cos α ^ 6 - 1 = -3 * (sin α ^ 2 * cos α ^ 2) by linarith [h7]]
  -- $\frac{-2 \cdot (sin \alpha ^ 2 \cdot cos \alpha ^ 2)}{-3 \cdot (sin \alpha ^ 2 \cdot cos \alpha ^ 2)} = \frac{2}{3}$
  field_simp [h8]
  <;> ring_nf
  <;> field_simp [h8]
  <;> ring