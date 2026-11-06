import Mathlib

theorem algebra_236211 (f : ℝ → ℝ) (hpos : ∀ x > 0, f x > 0)
    (hf1 : f 1 = 1) (hadd : ∀ a b, f (a + b) * (f a + f b) = 2 * f a * f b + a ^ 2 + b ^ 2) :
    ∀ x, f x = x := by

  have h0 : f 0 = 0 := by
    have h1 := hadd 1 0
    norm_num [hf1] at h1
    nlinarith

  have h1 : ∀ x > 0, f x ^ 2 = x ^ 2 := by
    intro x hx
    have h2 := hadd x 0
    simp [h0] at h2
    nlinarith

  have h2 : ∀ x > 0, f x = x := by
    intro x hx
    have h3 : f x > 0 := hpos x hx
    have h4 : f x ^ 2 = x ^ 2 := h1 x hx
    have h5 : f x = x := by
      nlinarith
    exact h5

  intro x
  by_cases h3 : x > 0
  · specialize h2 x h3
    linarith
  by_cases h4 : x < 0
  · -- Case x < 0
    have h5 : -x > 0 := by linarith
    have h6 : f (-x) = -x := h2 (-x) h5
    have h7 : f x * f (-x) = -x ^ 2 := by
      have h4 := hadd x (-x)
      have h5 : (x + (-x) : ℝ) = (0 : ℝ) := by ring
      rw [h5] at h4
      simp [h0] at h4
      linarith
    rw [h6] at h7
    have h8 : f x = x := by
      nlinarith
    linarith
  · -- Case x = 0
    have h9 : x = 0 := by linarith
    rw [h9]
    linarith [h0]