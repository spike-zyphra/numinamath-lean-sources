import Mathlib

theorem algebra_209002 {f : ℝ → ℝ} (h : ∀ x y, (f (x + y)) ^ 2 = f x ^ 2 + f y ^ 2) :
    ∀ x, f x = 0 := by

  have h1 : f 0 = 0 := by
    specialize h 0 0
    simp at h
    nlinarith
  
  intro x
  have h2 := h x (-x)
  simp [h1] at h2
  have h3 : f x ^ 2 ≥ 0 := by apply sq_nonneg
  have h4 : f (-x) ^ 2 ≥ 0 := by apply sq_nonneg
  have h5 : f x ^ 2 = 0 := by nlinarith
  have h6 : f x = 0 := by
    rw [sq_eq_zero_iff] at h5
    exact h5
  exact h6