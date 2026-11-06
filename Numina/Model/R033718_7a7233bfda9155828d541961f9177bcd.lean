import Mathlib

theorem algebra_118382 {f : ℝ → ℝ} (h : ∀ x, 2 * f (3 - 2 * x) + f (2 * x - 2) = x) :
    Function.Bijective f ∧ ∀ y, f y = (4 - 3 * y) / 6 := by
  have eq1 : ∀ y, 2 * f y + f (1 - y) = (3 - y) / 2 := by 
    intro y
    have h1 := h ((3 - y) / 2)
    have : 3 - 2 * ((3 - y) / 2) = y := by 
      ring
    rw [this] at h1
    have : 2 * ((3 - y) / 2) - 2 = (1 - y) := by 
      ring
    rw [this] at h1
    linarith
  have eq2 : ∀ y, 2 * f (1 - y) + f y = (y + 2) / 2 := by 
    intro y
    have h2 := h ((y + 2) / 2)
    have : 3 - 2 * ((y + 2) / 2) = (1 - y) := by 
      ring
    rw [this] at h2
    have : 2 * ((y + 2) / 2) - 2 = y := by 
      ring
    rw [this] at h2
    linarith
  have explicit : ∀ y, f y = (4 - 3 * y) / 6 := by 
    intro y
    have eq3 := eq1 y
    have eq4 := eq2 y
    linarith [eq3, eq4]
  constructor
  · -- Let's prove that f is bijective
    constructor
    · -- First, prove that f is injective
      intro x y hxy
      rw [explicit x, explicit y] at hxy
      linarith
    · -- Now, prove that f is surjective
      intro y
      use (4 / 3 - 2 * y)
      rw [explicit]
      ring
  · -- Now prove the formula
    intro y 
    apply explicit