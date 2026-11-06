import Mathlib

theorem algebra_17193 {graph : Set (ℝ × ℝ)} (h₀ : ∀ x y, (x, y) ∈ graph → x > 0 ∧ y > 0) (h₁ : ∃ c, ∀ x y, (x, y) ∈ graph → x^2 * y = c) (h₂ : (2, 10) ∈ graph) (h₃ : (x, 4000) ∈ graph) :
    x = 1 / 10 := by
  rcases h₁ with ⟨c, h₁⟩
  have h4 : (2 : ℝ) ^ 2 * (10 : ℝ) = c := h₁ 2 10 h₂
  have h5 : x ^ 2 * (4000 : ℝ) = c := h₁ x 4000 h₃
  norm_num at h4
  have hc : c = 40 := by linarith
  have hx1 : x > 0 := (h₀ x 4000 h₃).left
  rw [hc] at h5
  have h6 : x ^ 2 = 1 / 100 := by
    nlinarith
  have hx2 : x = 1 / 10 := by
    nlinarith [h6, hx1]
  exact hx2