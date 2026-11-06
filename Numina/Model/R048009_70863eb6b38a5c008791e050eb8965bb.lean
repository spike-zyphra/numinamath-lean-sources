import Mathlib

theorem algebra_104892 {f : ℝ → ℝ} (h : ∀ x y, f (y + f x) = (y - 1) * f x ^ 2 + 3 * x) :
    Function.Bijective f := by

  have h1 : ∀ x, f (f x) = - f x ^ 2 + 3 * x := by
    intro x
    specialize h x 0
    simpa using h

  have h2 : ∀ x, f (1 + f x) = 3 * x := by
    intro x
    specialize h x 1
    norm_num at h
    linarith

  constructor
  · -- f is injective
    intro a b h_eq
    have h3 : f (f a) = f (f b) := by
      rw [h_eq]
    have h4 : f (f a) = - f a ^ 2 + 3 * a := h1 a
    have h5 : f (f b) = - f b ^ 2 + 3 * b := h1 b
    rw [h4] at h3
    rw [h5] at h3
    have h6 : f a ^ 2 = f b ^ 2 := by
      have h7 : f a = f b := h_eq
      have h8 : f a ^ 2 = f b ^ 2 := by
        rw [h7]
      linarith
    have h7 : 3 * a = 3 * b := by
      nlinarith
    have h8 : a = b := by
      linarith
    exact h8
  · -- f is surjective
    intro y
    use 1 + f (y / 3)
    have h3 : f (1 + f (y / 3)) = 3 * (y / 3) := by
      apply h2
    have h4 : 3 * (y / 3) = y := by
      ring
    linarith [h3, h4]