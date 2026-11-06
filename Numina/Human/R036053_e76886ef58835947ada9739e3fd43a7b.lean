import Mathlib
/-Given that the point $(4,7)$ is on the graph of $y=3f\left(2x\right)+1$, there is one point that must be on the graph of $y=f(x)$. What is the sum of coordinates of that point?-/
theorem algebra_794 {f : ℝ → ℝ} (h : 7 = 3 * f (2 * 4) + 1) :
    ∃ x y, y = f x ∧ x + y = 10 := by
  have e₁ := sub_eq_zero.mpr h
  have e₂ : 7 - (3 * f (2 * 4) + 1) = 3 * (2 - f 8) := by ring_nf
  -- substitute (4, 7) 
  rw [e₂] at e₁
  rcases mul_eq_zero.mp e₁ with h₁ | h₁
  · norm_num at h₁
  -- simplify and get 2 = f (8)
  use 8
  use 2
  exact ⟨sub_eq_zero.mp h₁, (by norm_num)⟩