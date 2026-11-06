import Mathlib

theorem algebra_245086 (f : ℝ → ℝ) :
    (∀ x y, f (x + f y) = f (x + y) + 1) ∧ StrictMono f ↔ ∀ y, f y = y + 1 := by
  constructor
  · -- Assume (a) and (b), prove f(y) = y + 1
    rintro ⟨h_eq, h_mono⟩
    have h1 : ∀ x, f (x + f 0) = f x + 1 := by
      intro x
      specialize h_eq x 0
      simpa using h_eq
    -- Compute f(0)
    have h3 : ∀ y : ℝ, f (-y + f y) = f 0 + 1 := by
      intro y
      specialize h_eq (-y) y
      simp at h_eq
      linarith
    -- f(0) and h6 for linear
    have h4 : ∀ y1 y2 : ℝ, f y1 = f y2 → y1 = y2 := by
      intro y1 y2 h_eq_y1y2
      exact h_mono.injective h_eq_y1y2
    -- linear function
    have h5 : ∀ y : ℝ, f y = y + f 0 := by
      intro y
      have h6 : -y + f y = - (0 : ℝ) + f 0 := by
        have h_eq1 := h3 y
        have h_eq2 := h3 0
        have h_eq3 : f (-y + f y) = f (- (0 : ℝ) + f 0) := by
          linarith
        have h7 : -y + f y = - (0 : ℝ) + f 0 := by
          apply h4
          exact h_eq3
        exact h7
      linarith
    -- determine f(0)
    have hc : f 0 = 1 := by
      have h6 : f (f 0) = f 0 + 1 := by
        specialize h_eq 0 0
        simpa using h_eq
      have h7 : f (f 0) = 2 * f 0 := by
        have h8 : f (f 0) = f 0 + f 0 := by
          specialize h5 (f 0)
          simpa using h5
        linarith
      linarith [h6, h7]
    intro y
    specialize h5 y
    rw [hc] at h5
    linarith
  · -- Assume f(y) = y + 1 prove the conjunction of the two conditions.
    intro h_eq
    constructor
    · -- Show the functional equation holds
      intro x y
      have h_fy : f y = y + 1 := h_eq y
      have h_fxy : f (x + f y) = (x + f y) + 1 := by
        specialize h_eq (x + f y)
        simpa using h_eq
      have h_f_x_y : f (x + y) = (x + y) + 1 := by
        specialize h_eq (x + y)
        simpa using h_eq
      rw [h_fxy, h_f_x_y, h_eq y]
      <;> ring
    · -- Show that f is strictly increasing
      intro x y hxy
      have hfx : f x = x + 1 := h_eq x
      have hfy : f y = y + 1 := h_eq y
      rw [hfx, hfy]
      linarith