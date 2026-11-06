import Mathlib

theorem algebra_249628 (f : ℝ → ℝ) (hf : StrictMono f)
    (h : ∀ x y, f (x + f y) = f (x + y) + 1) :
    ∀ x, f x = x + 1 := by

  have h1 : ∀ x, f (x + f 0) = f x + 1 := by
    intro x
    specialize h x 0
    simpa using h

  have h2 : ∀ y, f (f y) = f y + 1 := by 
    intro y
    specialize h 0 y
    simpa using h

  have h3 : ∀ y, f (y - f y) = f 0 - 1 := by
    intro y
    have h4 := h (-f y) y
    have eq1 : (-f y : ℝ) + f y = (0 : ℝ) := by
      linarith
    have eq2 : (-f y : ℝ) + (y : ℝ) = y - f y := by
      linarith
    rw [eq1, eq2] at h4
    linarith

  have h4 : ∃ k : ℝ, ∀ y, y - f y = k := by
    use (0 - f 0)
    intro y 
    have h5 : f (y - f y) = f (0 - f 0) := by
      have h6 : f (y - f y) = f 0 - 1 := h3 y 
      have h7 : f (0 - f 0) = f 0 - 1 := h3 0
      linarith

    have h6 : y - f y = (0 - f 0) := by
      by_cases h7 : y - f y < (0 - f 0)
      · -- Since f is strictly increasing
        have h8 : f (y - f y) < f (0 - f 0) := by 
          apply hf.lt_iff_lt.mpr
          linarith
        linarith [h5, h8]
      by_cases h8 : y - f y > (0 - f 0)
      · -- Since f is strictly increasing
        have h9 : f (y - f y) > f (0 - f 0) := by 
          apply hf.lt_iff_lt.mpr
          linarith
        linarith [h5, h9]
      linarith
    linarith [h6]

  rcases h4 with ⟨k, hk⟩
  have h5 : ∀ y, f y = y - k := by
    intro y 
    linarith [hk y]

  have eq1 : k = -1 := by
    have eq2 := h2 0 
    rw [h5 0] at eq2 
    rw [h5 (0 - k)] at eq2 
    linarith

  have eq2 : ∀ y, f y = y + 1 := by 
    intro y
    rw [h5 y]
    linarith [eq1]

  intro x 
  specialize eq2 x 
  linarith