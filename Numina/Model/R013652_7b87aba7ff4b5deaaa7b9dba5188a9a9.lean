import Mathlib

theorem algebra_8771 (f : ℝ → ℝ) :
    (∀ x y z, f (x + y) + f (x + z) - f x * f (y + z) ≥ 1) ↔
    ∀ x, f x = 1 := by
  constructor
  · -- Assume the functional inequality, prove f(x) = 1 for all x
    intro h
    -- Prove f(0) = 1
    have h1 : f 0 = 1 := by
      have h2 := h 0 0 0
      simp at h2
      nlinarith [sq_nonneg (f 0 - 1)]
    -- Prove f(x) ≥ 1 for all x
    have h2 : ∀ x, f x ≥ 1 := by
      intro x
      have h3 := h x 0 0
      simp [h1] at h3
      linarith
    -- Prove f(-x) = 1 for all x
    have h3 : ∀ x, f (-x) = 1 := by
      intro x
      have h4 := h x (-x) (0 : ℝ)
      have h5 : f (x + (-x)) + f (x + (0 : ℝ)) - f x * f ((-x) + (0 : ℝ)) ≥ 1 := by simpa using h4
      have h6 : x + (-x) = (0 : ℝ) := by linarith
      have h7 : x + (0 : ℝ) = x := by linarith
      have h8 : (-x) + (0 : ℝ) = -x := by linarith
      rw [h6, h7, h8, h1] at h5
      have h5 : f x - f x * f (-x) ≥ 0 := by linarith
      have h5 : f x * (1 - f (-x)) ≥ 0 := by linarith
      have h10 : f (-x) ≤ 1 := by nlinarith [h2 x]
      have h11 : f (-x) ≥ 1 := h2 (-x)
      linarith
    -- Prove f(2x) = 1 for all x
    have h4 : ∀ x, f (2 * x) = 1 := by
      intro x
      have h5 := h (-x) x x
      have eq1 : (-x : ℝ) + x = (0 : ℝ) := by linarith
      have eq3 : x + x = (2 * x : ℝ) := by ring
      have eq4 : f ((-x : ℝ) + x) = f 0 := by
        rw [eq1]
      have eq5 : f (x + x) = f (2 * x) := by
        simp [eq3]
      simp only [eq4, eq5] at h5
      simp [h1, h3 x] at h5 
      have h7 : f (2 * x) ≤ (1 : ℝ) := by
        nlinarith
      have h8 : f (2 * x) ≥ (1 : ℝ) := h2 (2 * x)
      linarith
    -- Prove f(x) = 1 for all x
    intro x
    have h5 : f (2 * (x / 2 : ℝ)) = 1 := h4 (x / 2)
    have h6 : (2 * (x / 2 : ℝ) ) = x := by ring
    rw [h6] at h5
    linarith
  · -- Assume f(x) = 1 for all x, prove the functional inequality
    intro hf x y z
    simp [hf]
    all_goals linarith