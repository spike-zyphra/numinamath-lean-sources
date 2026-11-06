import Mathlib

theorem algebra_131878 {f : ℝ → ℝ} (h : ∀ x y, x + f (x * f y) = f y + y * f x) :
    ∀ x, f x = x - 1 := by

  have h1 : ∀ y, f y = f 0 - y * f 0 := by
    intro y
    specialize h 0 y
    simp at h
    linarith

  have h2 : ∀ x, x + f (x * f 0) = f 0 := by
    intro x
    specialize h x 0
    simp at h
    linarith

  have h5 : ∀ x, f (x * f 0) = f 0 - (x * f 0) * f 0 := by
    intro x
    specialize h1 (x * f 0)
    try linarith  -- handle algebraic simplification

  have h4 : ∀ x, x + (f 0 - (x * f 0) * f 0) = f 0 := by
    intro x
    specialize h2 x
    have h1' := h5 x
    linarith [h2, h1']

  have h5' : f 0 ^ 2 = 1 := by
    have eq1 := h4 1
    have eq2 := h4 (-1)
    nlinarith

  have h6 : f 0 = 1 ∨ f 0 = -1 := by
    have h5'': f 0 ^ 2 = 1 := h5'
    rw [sq_eq_one_iff] at h5''
    tauto

  cases h6 with
  | inl h01 =>
    -- Assume f 0 = 1, then we can derive contradiction

    have h7 : ∀ y, f y = 1 - y := by
      intro y
      specialize h1 y
      rw [h01] at h1
      linarith

    -- Show contradiction by using h
    specialize h 1 1
    simp [h7 1, h7 0] at h
    all_goals linarith

  | inr h01 =>
    -- Assume f 0 = -1, then we can prove f x = x - 1

    have h8 : ∀ y, f y = y - 1 := by
      intro y
      specialize h1 y
      rw [h01] at h1
      linarith

    intro x
    specialize h8 x
    linarith