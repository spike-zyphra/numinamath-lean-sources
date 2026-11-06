import Mathlib

theorem algebra_102340 {f : ℝ → ℝ} (h : ∀ x y, 2 * f x = f (x + y) + f (x + 2 * y)) :
    ∀ x, f x = f 0 := by
  intro x
  have eq1 : 2 * f x = f 0 + f (-x) := by
    specialize h x (-x)
    ring_nf at h ⊢
    linarith
  have eq2 : 2 * f (-x) = f 0 + f x := by 
    specialize h (-x) x
    ring_nf at h ⊢
    linarith
  linarith