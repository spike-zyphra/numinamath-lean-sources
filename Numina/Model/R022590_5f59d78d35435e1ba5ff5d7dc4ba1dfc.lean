import Mathlib

theorem inequalities_75516 (f : ℝ → ℝ) :
    (∀ x y z, (f (x * y) + f (x * z)) / 2 - f x * f (y * z) ≥ 1 / 4) ↔
    ∀ x, f x = 1 / 2 := by
  constructor
  · -- First, we verify that inequality holds implies f(x) = 1/2.
    intro h
    have h1 : f 0 = 1 / 2 := by
      have h2 := h 0 0 0
      simp at h2
      nlinarith [sq_nonneg (f 0 - 1 / 2)]
    intro x
    have h4 := h x 0 0
    simp [h1] at h4
    have h5 := h x 1 1
    simp at h5
    have h6 := h 1 1 1
    norm_num at h6
    have h7 : f 1 = 1 / 2 := by
      nlinarith [sq_nonneg (f 1 - 1 / 2)]
    have h8 : f x ≥ 1 / 2 := by
      nlinarith [h5, h7, sq_nonneg (f x - 1 / 2)]
    have h9 : f x ≤ 1 / 2 := by
      nlinarith
    linarith
  · -- Conversely, if f(x) = 1/2, then inequality holds.
    intro hf
    intro x y z
    have h1 : f (x * y) = 1 / 2 := by
      specialize hf (x * y)
      simpa using hf
    have h2 : f (x * z) = 1 / 2 := by
      specialize hf (x * z)
      simpa using hf
    have h3 : f x = 1 / 2 := by
      specialize hf x
      simpa using hf
    have h4 : f (y * z) = 1 / 2 := by
      specialize hf (y * z)
      simpa using hf
    rw [h1, h2, h3, h4]
    norm_num