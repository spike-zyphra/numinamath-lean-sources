import Mathlib

theorem algebra_309930 {f : ℝ → ℝ} (h : ∀ x y, f (x * f y) = x * y) :
    |f 1995| = 1995 := by
  have h1 : ∀ y, f (f y) = y := by
    intro y
    specialize h 1 y
    norm_num at h ⊢
    all_goals linarith
  -- Show that f(a * b) = a * f(b) for all a, b
  have h2 : ∀ x y, f (x * y) = x * f y := by
    intro x y
    have h3 : f (x * f (f y)) = x * (f y) := by
      apply h x (f y)
    have h4 : f (f y) = y := h1 y
    rw [h4] at h3
    linarith
  -- Show that f(x) = x * f(1)
  have h3 : ∀ x, f x = x * f 1 := by
    intro x
    have h4 : f (x * (1 : ℝ)) = x * f (1 : ℝ) := h2 x 1
    have h5 : x * (1 : ℝ) = x := by ring
    rw [h5] at h4
    linarith
  -- Show that f(1) ^ 2 = 1
  have h4 : f 1 * f 1 = 1 := by
    have h5 : f (f 1) = (1 : ℝ) := h1 1
    have h6 : f (f 1) = (f 1) * (f 1) := by
      rw [h3 (f 1)]
      all_goals ring
    rw [h6] at h5
    linarith
  -- Show that f(1) = 1 or f(1) = -1
  have h5 : f 1 = 1 ∨ f 1 = -1 := by
    have h6 : f 1 ^ 2 = 1 := by
      nlinarith [h4]
    have : f 1 = 1 ∨ f 1 = -1 := by
      rw [sq_eq_one_iff] at h6
      tauto
    assumption
  cases h5 with
  | inl h6 =>
    -- Case f(1) = 1, so f(x) = x for all x
    have h7 : f 1995 = (1995 : ℝ) := by
      have h8 : f 1995 = (1995 : ℝ) * f 1 := by
        rw [h3 1995]
      rw [h6] at h8
      nlinarith
    rw [h7]
    all_goals norm_num
  | inr h6 =>
    -- Case f(1) = -1, so f(x) = -x for all x
    have h7 : f 1995 = (-1995 : ℝ) := by
      have h8 : f 1995 = (1995 : ℝ) * f 1 := by
        rw [h3 1995]
      rw [h6] at h8
      nlinarith
    rw [h7]
    all_goals norm_num [abs_of_nonneg, abs_of_nonpos]