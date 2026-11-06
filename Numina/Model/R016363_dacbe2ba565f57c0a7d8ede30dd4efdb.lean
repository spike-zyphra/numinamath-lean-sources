import Mathlib

theorem algebra_13410 (a : ℕ → ℝ) (h₀ : a 0 = 2) (h₁ : a 1 = 1 / 4)
    (h₂ : ∀ n, a (n + 1) = a n * (a 1 / a 0)) :
    a 4 = 1 / 2048 := by
  have ha2 : a 2 = a 1 * (a 1 / a 0) := h₂ 1
  rw [h₁, h₀] at ha2
  have ha2' : a 2 = 1 / 32 := by
    norm_num at ha2 ⊢
    linarith
  have ha3 : a 3 = a 2 * (a 1 / a 0) := h₂ 2
  rw [ha2', h₁, h₀] at ha3
  have ha3' : a 3 = 1 / 256 := by
    norm_num at ha3 ⊢
    linarith
  have ha4 : a 4 = a 3 * (a 1 / a 0) := h₂ 3
  rw [ha3', h₁, h₀] at ha4
  norm_num at ha4 ⊢
  all_goals linarith