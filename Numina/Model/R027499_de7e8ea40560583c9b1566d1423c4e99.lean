import Mathlib

theorem algebra_294215 {f : ℝ → ℝ} (h : ∀ x y, f (f x) + f (f y) = 2 * y + f (x - y)) :
    ∀ x, f x = x := by

  have h1 : ∀ x, f (f x) = x + f 0 / 2 := by
    intro x
    have h2 := h x x
    simp at h2 ⊢
    linarith
  have h2 : ∀ x, f (f x) = f x - f (f 0) := by
    intro x
    have h3 := h x 0
    simp at h3 ⊢
    linarith
  have h3 : f (f 0) = f 0 / 2 := by 
    specialize h1 0
    simpa using h1
  -- We have f x = x + f 0 for all x.
  have h4 : ∀ x, f x = x + f 0 := by
    intro x
    have eq1 : f (f x) = x + f 0 / 2 := h1 x
    have eq2 : f (f x) = f x - f (f 0) := h2 x
    have eq3 : f (f 0) = f 0 / 2 := h3
    have eq4 : f x = x + f 0 := by
      rw [eq3] at eq2
      linarith [eq1, eq2]
    exact_mod_cast eq4

  have eq5 : f (f 1) + f (f 0) = f 1 := by
    specialize h 1 0
    norm_num at h ⊢
    simpa using h
  have eq6 : f 1 = 1 + f 0 := by
    specialize h4 1
    norm_num at h4 ⊢
    linarith
  have eq7 : f (f 0) = f 0 / 2 := h3
  have eq8 : f (f 1) = 1 + 2 * f 0 := by
    have h8 : f 1 = 1 + f 0 := eq6
    have h9 : f (f 1) = (1 + f 0) + f 0 := by
      rw [show f 1 = 1 + f 0 by linarith [h8]]
      have h4' := h4 (1 + f 0)
      simpa using h4'
    linarith
  -- Now, use these to solve for f 0 = 0.
  have h5 : f 0 = 0 := by
    rw [eq8, eq7, eq6] at eq5
    linarith
  -- Now that we have f 0 = 0, we can show f x = x for all x.
  have h6 : ∀ x, f x = x := by
    intro x
    specialize h4 x
    rw [h5] at h4
    linarith
  exact_mod_cast h6