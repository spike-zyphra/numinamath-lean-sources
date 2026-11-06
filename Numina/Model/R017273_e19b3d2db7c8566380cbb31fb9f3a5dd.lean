import Mathlib

theorem algebra_236344 (f : ℝ → ℝ) (h₀ : ∀ x > 0, f x > 0)
    (h₁ : f 1 = 1) (h₂ : ∀ a b, f (a + b) * (f a + f b) = 2 * f a * f b + a ^ 2 + b ^ 2) :
    ∀ x, f x = x := by

  have h3 : f 0 = 0 := by
    have eq1 := h₂ 1 0
    simp at eq1
    rw [h₁] at eq1
    nlinarith [h₀ 1 (by norm_num)]

  have h4 : ∀ a, f a ^ 2 = a ^ 2 := by
    intro a
    have eq1 := h₂ a 0
    simp [h3] at eq1
    nlinarith

  have h5 : ∀ x > 0, f x = x := by
    intro x hx
    have h6 : f x ^ 2 = x ^ 2 := h4 x
    have h7 : f x > 0 := h₀ x hx
    nlinarith [sq_nonneg (f x - x)]

  intro x
  by_cases h : x > 0
  · -- Case x > 0
    specialize h5 x h
    simpa using h5

  by_cases h' : x = 0
  · -- Case x = 0
    rw [h']
    linarith [h3]

  · -- Case x ≤ 0 and x ≠ 0, so x < 0
    have h6 : x < 0 := by
      by_contra h6
      push_neg at h6
      have : x = 0 := by linarith
      tauto

    have h7 : f (-x) = -x := by
      have h8 : -x > 0 := by linarith
      specialize h5 (-x) h8
      nlinarith

    -- Now, use the functional equation with $a = x$ and $b = -x$
    have h8 : f x = x := by
      have eq1 := h₂ x (-x)
      have h9 : x + (-x) = (0 : ℝ) := by
        ring
      rw [h9] at eq1
      simp [h3, h7] at eq1
      have h10 : x ≠ 0 := by linarith
      apply (mul_left_inj' h10).mp
      linarith
    exact h8