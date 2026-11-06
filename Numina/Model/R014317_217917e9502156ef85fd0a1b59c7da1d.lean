import Mathlib


theorem algebra_258321 {f : ℝ → ℝ} (h : ∀ x y, f (x * f y + 1) = y + f (f x * f y)) :
    ∀ x, f x = x - 1 := by

  have h1 : ∀ a b : ℝ, f a = f b → a = b := by
    intro a b hab
    have h2 : ∀ x : ℝ, f (x * f a + 1) = a + f (f x * f a) := by
      intro x
      specialize h x a
      simpa using h
    have h3 : ∀ x : ℝ, f (x * f b + 1) = b + f (f x * f b) := by
      intro x
      specialize h x b
      simpa using h
    have h4 : ∀ x : ℝ, a + f (f x * f a) = b + f (f x * f b) := by
      intro x
      have h5 : f (x * f a + 1) = f (x * f b + 1) := by
        have : f (x * f a + 1) = f (x * f b + 1) := by
          have h11 : f a = f b := by linarith [hab]
          simp [h11]
        assumption
      have h6 : f (x * f a + 1) = a + f (f x * f a) := h2 x
      have h7 : f (x * f b + 1) = b + f (f x * f b) := h3 x
      linarith [h5, h6, h7]

    have h8 : a = b := by
      have h9 : a + f (f 0 * f a) = b + f (f 0 * f b) := h4 0
      have h10 : f (f 0 * f a) = f (f 0 * f b) := by
        have h11 : f a = f b := by linarith [hab]
        have h12 : f (f 0 * f a) = f (f 0 * f b) := by
          have h13 : f 0 * f a = f 0 * f b := by
            rw [show f a = f b by linarith [hab]]
          rw [h13]
        assumption
      nlinarith
    assumption

  have h2 : ∀ x : ℝ, x * f 0 + 1 = f x * f 0 := by
    intro x
    have h3 : f (x * f 0 + 1) = f (f x * f 0) := by
      specialize h x 0
      simpa using h
    have h4 : x * f 0 + 1 = f x * f 0 := by
      apply h1
      all_goals
      linarith [h3]
    linarith

  have h3 : f 0 ≠ 0 := by
    by_contra h3
    have h4 : 1 = (0 : ℝ) := by
      have h5 : 0 * f 0 + 1 = f 0 * f 0 := by
        apply h2 0
      rw [h3] at h5
      nlinarith
    linarith

  have h4 : f 0 = -1 := by
    have h5 : f 0 * (f 0 + 1) = 0 := by
      have h7 : f 1 = (f 0 + 1) / f 0 := by
        have h71 : f 0 + 1 = f 1 * f 0 := by
          have h711 : 1 * f 0 + 1 = f 1 * f 0 := by
            apply h2 1
          nlinarith
        have h8 : f 0 ≠ 0 := h3
        field_simp at *
        nlinarith

      have h8 : f 1 = 1 + f (f 0 * f 1) := by
        have h7 : f (0 * f 1 + 1) = (1 : ℝ) + f (f 0 * f 1) := by
          specialize h 0 1
          simpa using h
        norm_num at h7 ⊢
        linarith

      have h9 : f 0 * (f 0 * f 1) + 1 = f (f 0 * f 1) * f 0 := by
        have h10 : (f 0 * f 1) * f 0 + 1 = f (f 0 * f 1) * f 0 := by
          apply h2 (f 0 * f 1)
        nlinarith

      have h10 : f (f 0 * f 1) = f 1 - 1 := by linarith [h8]

      rw [h10] at h9

      rw [h7] at h9

      field_simp [show f 0 ≠ 0 by assumption] at h9 ⊢
      nlinarith [sq_pos_of_ne_zero (show f 0 ≠ 0 by assumption)]

    cases' (mul_eq_zero.mp h5) with h17 h18
    · 
      exfalso
      apply h3
      linarith
    · 
      linarith

  have h5 : ∀ x, f x = x - 1 := by
    intro x
    have h6 : x * f 0 + 1 = f x * f 0 := h2 x
    rw [show f 0 = -1 by linarith [h4]] at h6
    nlinarith

  intro x
  apply h5 x