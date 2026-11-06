import Mathlib


theorem algebra_298514 {f : ℝ → ℝ} (h0 : f 0 ≠ 0)
    (h : ∀ x y, f ((x - y) ^ 2) = (f x) ^ 2 - 2 * x * f y + y ^ 2) :
    f 2012 = 2013 := by

  have h1 : f 0 = 1 := by
    have h2 := h 0 0
    norm_num at h2
    have h3 : f 0 * (f 0 - 1) = 0 := by
      linarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- f 0 = 0, contradiction
      exfalso
      exact h0 (by linarith)
    · -- f 0 - 1 = 0
      linarith

  have h3 : ∀ x : ℝ, f x = x + 1 := by
    intro x
    have h4 : (f x) ^ 2 - 2 * x * (f x) + x ^ 2 = 1 := by
      have h3 := h x x
      simp [h1] at h3 ⊢
      linarith

    have h10 : f x = x + 1 ∨ f x = x - 1 := by
      have h8 : (f x - (x + 1)) * (f x - (x - 1)) = 0 := by
        nlinarith
      cases (mul_eq_zero.1 h8) with
      | inl h11 =>
        left
        linarith
      | inr h12 =>
        right
        linarith

    cases h10 with
    | inl h11 =>
      tauto
    | inr h12 =>
      have h7 : f (x ^ 2) = x ^ 2 + 1 := by
        have h8 : f (x ^ 2) = 1 + x ^ 2 := by
          have h9 := h 0 x
          norm_num at h9 ⊢
          nlinarith [h1]
        linarith

      have h6 : f (x ^ 2) = (f x) ^ 2 - 2 * x := by
        specialize h x 0
        simp [h1] at h ⊢
        linarith

      rw [h12] at h6
      have h13 : x = 0 := by
        nlinarith [h7, h6]

      have h14 : f 0 = -1 := by
        rw [h13] at h12
        linarith

      linarith [h1, h14]

  specialize h3 2012
  linarith