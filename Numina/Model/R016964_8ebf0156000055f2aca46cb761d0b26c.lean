import Mathlib

theorem algebra_104874 (f : ℝ → ℝ) (h : ∀ x y, f (x - f y) = 1 - x - y) :
    ∀ x, f x = (1 / 2) - x := by

  have h1 : ∀ x y, f x = f y → x = y := by
    intro x y h_eq
    have h2 := h 0 x
    have h3 := h 0 y
    have h4 : f (0 - f x) = 1 - (0 : ℝ) - x := by
      simpa using h2
    have h5 : f (0 - f y) = 1 - (0 : ℝ) - y := by
      simpa using h3
    have h6 : 0 - f x = 0 - f y := by
      have h7 : f x = f y := by
        simpa using h_eq
      linarith [h7]
    have h7 : f (0 - f x) = f (0 - f y) := by
      rw [h6]
    have h8 : (1 - (0 : ℝ) - x) = (1 - (0 : ℝ) - y) := by
      linarith [h4, h5, h7]
    linarith

  have h2 : ∀ y, f 0 = 1 - f y - y := by
    intro y
    have h3 := h (f y) y
    have h4 : f y - f y = (0 : ℝ) := by
      ring_nf
    have h5 : f (f y - f y) = f 0 := by
      rw [show f y - f y = (0 : ℝ) by linarith]
    have h8 : f (f y - f y) = 1 - f y - y := by
      simpa using h3
    linarith [h8, h5]

  have h3 : f 0 = 1 / 2 := by
    have h4 := h2 0
    norm_num at h4 ⊢
    linarith

  intro x
  have h4 := h2 x
  rw [h3] at h4
  linarith