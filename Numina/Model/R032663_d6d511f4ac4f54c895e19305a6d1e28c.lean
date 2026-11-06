import Mathlib

theorem algebra_112896 {f : ℝ → ℝ} (h : ∀ x y, f x * f y = f (x - y)) :
    ∀ x, f x = 0 ∨ f x = 1 := by

  -- First, let's compute f(0).
  have h1 : f 0 * f 0 = f (0 - 0) := h 0 0
  have h2 : f (0 - 0) = f 0 := by simp
  rw [h2] at h1
  have h3 : f 0 * (f 0 - 1) = 0 := by
    nlinarith
  have h00 : f 0 = 0 ∨ f 0 = 1 := by
    cases (mul_eq_zero.1 h3) with
    | inl h4 => 
      left
      linarith
    | inr h5 =>
      right
      linarith

  -- Show that for all x, f(x)^2 = f(0)
  have h3 : ∀ x, f x * f x = f 0 := by 
    intro x
    specialize h x x
    have h4 : f x * f x = f (x - x) := h
    have h5 : x - x = (0 : ℝ) := by 
      simp
    rw [h5] at h4
    linarith

  intro x
  have eq1 : f x * f x = f 0 := h3 x
  rcases h00 with (h00 | h00)
  · -- Case f 0 = 0
    have h5 : f x * f x = 0 := by 
      rw [h00] at eq1 
      linarith 
    have h6 : f x = 0 := by 
      nlinarith 
    left
    exact h6
  · -- Case f 0 = 1
    have h5 : f x * f x = 1 := by 
      rw [h00] at eq1 
      linarith 
    have h5' : f x * f (x / 2) = f (x - (x / 2)) := by 
      apply h x (x / 2)
    have h6 : x - (x / 2) = x / 2 := by 
      ring
    rw [h6] at h5'
    have eq2 : f x * f (x / 2) = f (x / 2) := h5'
    have h7 : f (x / 2) * (f x - 1) = 0 := by 
      linarith [eq2]
    -- Show that f(x / 2) ≠ 0
    have h8 : f (x / 2) * f (x / 2) = 1 := by
      specialize h3 (x / 2)
      rw [h00] at h3 
      linarith 
    have h9 : f (x / 2) ≠ 0 := by 
      by_contra h10 
      rw [h10] at h8 
      nlinarith 
    -- From f(x/2)(f(x) - 1) = 0 and f(x/2) ≠ 0, deduce f(x) - 1 = 0
    have h10 : f x - 1 = 0 := by 
      apply (mul_left_inj' h9).mp
      linarith 
    -- Therefore f(x) = 1
    have h11 : f x = 1 := by 
      linarith 
    right 
    exact h11