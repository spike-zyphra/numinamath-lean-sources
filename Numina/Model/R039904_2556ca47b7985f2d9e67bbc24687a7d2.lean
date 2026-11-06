import Mathlib

theorem algebra_129313 {f : ℝ → ℝ} (h : ∀ x y, f (f (x + y)) = f x + y) :
    ∀ x, f x = x := by
  have h1 : f (f 0) = f 0 := by
    specialize h 0 0
    norm_num at h ⊢
    all_goals linarith

  -- Setting x = 0 and y = t in h
  have h2 : ∀ t : ℝ, f (f t) = f 0 + t := by
    intro t
    specialize h 0 t
    simp at h ⊢
    linarith

  -- Setting y = 0 in h
  have h3 : ∀ x : ℝ, f (f x) = f x := by
    intro x
    specialize h x 0
    norm_num at h ⊢
    all_goals linarith

  -- From h3 and h2, we can derive f x = x + f 0
  have h4 : ∀ x : ℝ, f x = x + f 0 := by
    intro x
    have eq1 := h3 x
    have eq2 := h2 x
    have eq3 : f x = f 0 + x := by
      linarith [eq1, eq2]
    linarith

  -- Prove f 0 = 0
  have h5 : f 0 = 0 := by
    have eq1 := h3 0
    have eq2 := h4 0
    have eq3 := h4 (f 0)
    norm_num at eq1 eq2 eq3
    all_goals linarith

  intro x
  have eq1 := h4 x
  rw [h5] at eq1
  linarith