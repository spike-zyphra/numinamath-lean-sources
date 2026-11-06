import Mathlib

theorem algebra_296384 {f g : ℝ → ℝ}
    (hf : ∀ x, f (-x) = - f x) (hg : ∀ x, g (-x) = - g x) :
    ∀ x, (f + g) (-x) = -(f + g) x := by 
  intro x 
  simp [hf, hg]
  <;> ring