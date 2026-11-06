import Mathlib

theorem algebra_11315 {p q : ℝ → ℝ} (hp : ∃ a b, p = fun x => a * x + b)
    (hq : ∃ c d e, q = fun x => c * x ^ 2 + d * x + e)
    (h : ∀ x, p x / q x = (2 * x / ((x - 2) * (x + 3)))) :
    p (-1) / q (-1) = 1 / 3 := by

  have eq1 := h (-1)
  norm_num at eq1 ⊢
  <;> linarith