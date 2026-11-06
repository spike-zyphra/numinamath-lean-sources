import Mathlib

theorem algebra_199347 {f : ℝ → ℝ} (h : ∀ x y, f (x - y) = f x * f y) :
    (∀ x, f x = 0) ∨ (∀ x, f x = 1) := by
  have h00 : f 0 = f 0 * f 0 := by
    specialize h 0 0
    norm_num at h ⊢
    linarith

  have h1 : f 0 = 0 ∨ f 0 = 1 := by
    have : f 0 * (f 0 - 1) = 0 := by linarith
    cases (mul_eq_zero.mp this) with
    | inl h2 =>
      left
      linarith
    | inr h3 =>
      right
      linarith

  cases h1 with
  | inl h0 =>
    have h2 : ∀ x, f x = 0 := by
      intro x
      have h3 := h x x
      have h4 : f (x - x) = f x * f x := by
        simpa using h3
      have h5 : f (x - x) = f 0 := by
        simp
      rw [h5, h0] at h4
      nlinarith

    left
    exact h2
  | inr h0 =>
    have h2 : ∀ x, f x ^ 2 = 1 := by
      intro x
      have h3 := h x x
      have h4 : f (x - x) = f x * f x := by
        simpa using h3
      have h5 : f (x - x) = f 0 := by
        simp
      rw [h5, h0] at h4
      nlinarith

    have h3 : ∀ x, f x = 1 := by
      intro x
      have h4 : f x ^ 2 = 1 := h2 x
      have h5 : f (x / 2) ^ 2 = 1 := h2 (x / 2)
      have h6 : f (x - (x / 2)) = f x * f (x / 2) := h x (x / 2)
      have h7 : f (x - (x / 2)) = f (x / 2) := by
        ring_nf
      rw [h7] at h6
      have h8 : f (x / 2) * (1 - f x) = 0 := by
        nlinarith
      cases (mul_eq_zero.mp h8) with
      | inl h9 =>
        nlinarith [h5, h9]
      | inr h10 =>
        linarith
    right
    exact h3