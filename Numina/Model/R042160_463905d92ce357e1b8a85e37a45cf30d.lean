import Mathlib

theorem algebra_225276 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f (x ^ 2) + f (2 * y)) :
    f 1985 = 0 := by
  have h1 : f 0 = 0 := by
    specialize h 0 0
    norm_num at h
    linarith

  have h2 : ∀ x : ℝ, f x = f (x ^ 2) := by
    intro x
    specialize h x 0
    simp [h1] at h
    linarith

  have h3 : ∀ y : ℝ, f y = f (2 * y) := by
    intro y
    specialize h 0 y
    simp [h1] at h
    linarith

  have h4 : ∀ x y : ℝ, f (x + y) = f x + f y := by
    intro x y
    have eq1 : f (x + y) = f (x ^ 2) + f (2 * y) := h x y
    have eq2 : f (x ^ 2) = f x := by
      specialize h2 x
      linarith
    have eq3 : f (2 * y) = f y := by
      specialize h3 y
      linarith
    rw [eq2, eq3] at eq1
    linarith

  have h5 : ∀ x : ℝ, f x = 0 := by
    intro x
    have eq1 : f x = f (2 * x) := by
      specialize h3 x
      linarith
    have eq2 : f (2 * x) = 2 * f x := by
      have eq3 : f (2 * x) = f (x + x) := by ring_nf
      rw [eq3]
      have eq4 : f (x + x) = f x + f x := by
        apply h4
      rw [eq4]
      all_goals ring
    have eq3 : f x = 2 * f x := by
      linarith [eq1, eq2]
    linarith

  specialize h5 1985
  linarith