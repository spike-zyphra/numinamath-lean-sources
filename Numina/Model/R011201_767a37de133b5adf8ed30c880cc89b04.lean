import Mathlib

theorem algebra_104907 {f : ℝ → ℝ} (h : ∀ x y, f (2 * f x + f y) = 2 * x + f y) :
    ∀ x, f x = x := by
  have h_inj : ∀ x y, f x = f y → x = y := by
    intro x y h_eq
    have h1 := h x 0
    have h2 := h y 0
    have h3 : 2 * x + f 0 = 2 * y + f 0 := by
      have h4 : f (2 * f x + f 0) = 2 * x + f 0 := by
        simpa using h1
      have h5 : f (2 * f y + f 0) = 2 * y + f 0 := by
        simpa using h2
      have h6 : 2 * f x + f 0 = 2 * f y + f 0 := by
        have h7 : f x = f y := h_eq
        linarith
      have h8 : f (2 * f x + f 0) = f (2 * f y + f 0) := by
        rw [h6]
      rw [h4] at h8
      rw [h5] at h8
      linarith
    linarith
  have h1 : ∀ y, f (2 * f 0 + f y) = f y := by
    intro y
    specialize h 0 y
    simpa using h
  have h2 : ∀ y, 2 * f 0 + f y = y := by
    intro y
    have h3 : f (2 * f 0 + f y) = f y := h1 y
    have h4 : 2 * f 0 + f y = y := by
      apply h_inj (2 * f 0 + f y) y h3
    linarith
  have h3 : f 0 = 0 := by
    have h4 : 2 * f 0 + f 0 = (0 : ℝ) := by
      specialize h2 0
      simpa using h2
    linarith
  intro x
  have h5 : f x = x := by
    have h6 : 2 * f 0 + f x = x := by
      specialize h2 x
      linarith
    rw [h3] at h6
    linarith
  exact h5