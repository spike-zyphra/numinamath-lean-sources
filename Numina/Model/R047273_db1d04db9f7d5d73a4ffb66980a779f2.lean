import Mathlib

theorem algebra_50657 :
    ¬∃ f g : Polynomial ℝ, ∀ x y : ℝ, x^200 * y^200 + 1 = f.eval x * g.eval y := by 
  rintro ⟨f, g, h⟩
  have h1 := h 0 0
  have h2 := h 1 1
  have h3 := h 0 1
  have h4 := h 1 0
  norm_num at h1 h2 h3 h4
  have h9 : g.eval 0 = g.eval 1 := by
    have h10 : f.eval 0 ≠ 0 := by
      by_contra h'
      rw [h'] at h1 h3
      nlinarith
    have h11 : g.eval 0 = g.eval 1 := by
      apply (mul_left_inj' h10).mp
      linarith
    exact h11
  have h10 : f.eval 1 * g.eval 0 = 1 := by linarith
  have h11 : f.eval 1 * g.eval 1 = 2 := by linarith
  have h12 : g.eval 1 = g.eval 0 := by 
    linarith [h9]
  rw [h12] at h11
  nlinarith