import Mathlib

theorem algebra_10941 (f : ℝ → ℝ) :
    (∀ x y z, f (x * y) + f (x * z) - f x * f (y * z) ≥ 1) ↔
    ∀ x, f x = 1 := by 
  constructor
  · -- Assume that $f$ satisfies the inequality for all $x, y, z$.
    intro h
    have h1 : f 0 = 1 := by
      have h000 := h 0 0 0
      simp at h000
      nlinarith [sq_nonneg (f 0 - 1)]
    have h2 : ∀ x, f x ≤ 1 := by
      intro x
      have h00 := h x 0 0
      simp [h1] at h00
      linarith
    have h3 : ∀ x, f x ≥ 1 := by
      intro x
      have h111 := h x 1 1
      have h1_eq : f 1 = 1 := by
          have h1111 := h 1 1 1
          simp at h1111
          nlinarith [sq_nonneg (f 1 - 1)]
      simp [h1_eq] at h111
      linarith
    intro x 
    linarith [h2 x, h3 x]
  · -- Assume $f(x) = 1$ for all $x$.
    intro hf x y z
    have h1 : f (x * y) = 1 := by
      specialize hf (x * y)
      simpa using hf
    have h2 : f (x * z) = 1 := by
      specialize hf (x * z)
      simpa using hf
    have h3 : f x = 1 := by
      specialize hf x 
      simpa using hf
    have h4 : f (y * z) = 1 := by
      specialize hf (y * z)
      simpa using hf
    rw [h1, h2, h3, h4]
    all_goals linarith