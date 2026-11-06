import Mathlib

theorem algebra_278194 {f g : ℝ → ℝ}
    (h₁ : ∀ x, f (1 - x) = f (1 + x))
    (h₂ : ∀ x, g (1 - x) = -g (1 + x) - 4)
    (h₃ : ∀ x, f x + g x = 9 ^ x + x ^ 3 + 1) :
    f 2 * g 2 = 2016 := by
  have h1 := h₃ 2
  have h2 := h₃ 0
  have h3 := h₁ 1
  have h4 := h₂ 1
  norm_num at h1 h2
  norm_num at h3 h4
  have eq1 : f 0 = f 2 := by linarith
  have eq2 : g 0 = -g 2 - 4 := by linarith
  rw [eq1, eq2] at h2
  have eq3 : f 2 = 48 := by
    linarith [h1, h2]
  have eq4 : g 2 = 42 := by
    linarith [h1, eq3]
  rw [eq3, eq4]
  norm_num