import Mathlib

theorem algebra_154072 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y) :
    f 0 = 0 ∧ (∀ x, f (-x) = -f x) := by
  constructor
  · -- Proof that f(0) = 0
    have h1 : f 0 = 0 := by
      have eq1 : f (0 + 0) = f 0 + f 0 := h 0 0
      simp at eq1
      linarith
    exact h1
  · -- Proof that ∀ x, f(-x) = -f(x)
    intro x
    have h2 : f (x + (-x)) = f x + f (-x) := h x (-x)
    have eq1 : f (x + (-x)) = f 0 := by
      simp
    have h1 : f 0 = 0 := by
      have eq1 : f (0 + 0) = f 0 + f 0 := h 0 0
      simp at eq1
      linarith
    rw [eq1] at h2
    rw [h1] at h2
    linarith
    all_goals linarith
    all_goals linarith