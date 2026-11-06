import Mathlib

theorem algebra_127461 (f : ℝ → ℝ) : (∀ x y, f (x + y) = x * f x + y * f y) ↔ ∀ x, f x = 0 := by
  constructor
  · -- Assume f satisfying the relation, prove f(x) = 0
    intro h
    have h1 : f 0 = 0 := by
      specialize h 0 0
      norm_num at h
      linarith

    have h2 : ∀ x, f x = x * f x := by
      intro x
      specialize h x 0
      simp [h1] at h
      linarith

    have h3 : f (-1) = 0 := by
      have h4 := h2 (-1)
      norm_num at h4
      linarith

    intro x
    have h4 : f x = x * f x := h2 x
    have h5 : f x * (1 - x) = 0 := by
      linarith [h4]

    have h6 : f 1 = 0 := by
      have h7 := h 1 (-1)
      simp [h3, h1] at h7
      linarith

    by_cases h7 : x = 1
    · -- Case x = 1
      rw [h7]
      exact h6
    · -- Case x ≠ 1
      have h8 : x ≠ 1 := by
        intro h
        apply h7
        linarith

      have h9 : 1 - x ≠ 0 := by
        intro h10
        apply h8
        linarith

      have h10 : f x = 0 := by
        apply (mul_right_inj' h9).mp
        linarith

      exact h10
  · -- Assume f(x) = 0 for all x, prove the relation
    intro h x y
    simp [h x, h y, h (x + y)]
    all_goals linarith