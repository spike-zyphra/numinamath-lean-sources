import Mathlib

theorem algebra_126868 (f : ℝ → ℝ) :
    (∀ x y z, f (x * y) + f (x * z) ≥ 1 + f x * f (y * z)) ↔ ∀ x, f x = 1 := by
  constructor
  · -- Assume f satisfies the functional inequality, prove f(x) = 1 for all x
    intro h
    have f0 : f 0 = 1 := by
      have h1 := h 0 0 0
      simp at h1
      nlinarith [sq_nonneg (f 0 - 1)]
    have h_le_one : ∀ x, f x ≤ 1 := by
      intro x
      have h2 := h x 0 0
      simp [f0] at h2
      linarith
    have f1 : f 1 = 1 := by
      have h3 := h 1 1 1
      simp at h3
      nlinarith [sq_nonneg (f 1 - 1)]
    have h_ge_one : ∀ x, f x ≥ 1 := by
      intro x
      have h4 := h x 1 1
      simp [f1] at h4
      linarith
    intro x
    have h1 := h_le_one x
    have h2 := h_ge_one x
    linarith
  · -- Reverse implication: if f(x) = 1 for all x, then it satisfies the inequality
    intro hf x y z
    have hx : f x = 1 := hf x
    have hy : f y = 1 := hf y
    have hz : f z = 1 := hf z
    have hxy : f (x * y) = 1 := hf (x * y)
    have hxz : f (x * z) = 1 := hf (x * z)
    have hyz : f (y * z) = 1 := hf (y * z)
    rw [hxy, hxz, hx, hyz]
    all_goals linarith