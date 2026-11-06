import Mathlib

theorem algebra_12414 {f : ℝ → ℝ} (h1 : f 1 = 1) (h2 : ∀ x ∈ Set.Ioo 0 1, f x > 0)
    (h3 : ∀ x y : ℝ, f (x + y) - f (x - y) = 2 * f (1 - x) * f y) :
    f (1 / 3) = 1 / 2 := by
  have h4 : f 0 = 0 := by
    have eq1 := h3 1 0
    norm_num at eq1
    nlinarith [h1]
  have h5 := h3 (2 / 3 : ℝ) (1 / 3 : ℝ)
  have eq1 : f 1 - f (1 / 3 : ℝ) = 2 * f (1 / 3 : ℝ) * f (1 / 3 : ℝ) := by
    ring_nf at h5 ⊢
    <;> norm_num [h1, h4] at h5 ⊢
    <;> nlinarith
  have h6 : f (1 / 3 : ℝ) > 0 := by
    apply h2
    norm_num
  have eq3 : 2 * (f (1 / 3 : ℝ)) ^ 2 + f (1 / 3 : ℝ) - 1 = (0 : ℝ) := by
    rw [show f 1 = (1 : ℝ) by linarith [h1]] at eq1
    linarith
  have h8 : f (1 / 3 : ℝ) = 1 / 2 := by
    have h9 : (f (1 / 3 : ℝ) - 1 / 2) * (f (1 / 3 : ℝ) + 1) = 0 := by
      nlinarith [eq3]
    cases' (mul_eq_zero.mp h9) with h10 h11
    · linarith
    · linarith [h6]
  exact h8