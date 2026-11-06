import Mathlib

theorem algebra_191595 (f : ℝ → ℝ) :
    (∀ a b : ℕ, f a + f (a + b) - f (a - b) = a^2 + 4 * b + 2) ↔
    False := by
  constructor
  · -- Assume the functional equation holds for all natural numbers a, b.
    intro h
    have h1 := h 0 0
    norm_num at h1
    have h2 := h 0 1
    norm_num at h2
    have h3 := h 1 1
    norm_num at h3
    have h4 := h 2 0
    norm_num at h4
    have h5 := h 1 2
    norm_num at h5
    have h6 := h 3 0
    norm_num at h6
    have eq1 : f (1 : ℝ) - f (-1 : ℝ) = 4 := by
      linarith
    have eq2 : f (1 : ℝ) + f (2 : ℝ) = 9 := by 
      linarith [h1, h3]
    have eq3 : f (2 : ℝ) = 6 := by 
      linarith
    have eq4 : f (1 : ℝ) + f (3 : ℝ) - f (-1 : ℝ) = 11 := by 
      linarith
    have eq5 : f (3 : ℝ) = 7 := by
      linarith [eq1, eq4]
    have eq6 : f (3 : ℝ) = 11 := by 
      linarith
    linarith [eq5, eq6]
  · -- The converse direction: `False` implies anything.
    intro h
    cases h