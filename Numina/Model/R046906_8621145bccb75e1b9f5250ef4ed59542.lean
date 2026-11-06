import Mathlib

theorem algebra_198574 (t : ℝ) (f : ℝ → ℝ) (h₀ : f 0 = 1 / 2)
    (h₁ : ∀ x y, f (x + y) = f x * f (t - y) + f y * f (t - x)) :
    ∃ c, ∀ x, f x = c := by

  have h2 : f t = 1 / 2 := by
    have h2 := h₁ 0 0
    simp [h₀] at h2
    linarith

  have h3 : ∀ x, f x = f (t - x) := by
    intro x
    have h4 := h₁ x 0
    simp [h₀, h2] at h4
    linarith

  have h4 : ∀ x, f x ^ 2 = 1 / 4 := by
    intro x
    have h5 := h₁ x (t - x)
    have h6 : x + (t - x) = t := by ring
    rw [h6] at h5
    have h7 : f (t - (t - x)) = f x := by
      have h8 : t - (t - x) = x := by ring
      rw [h8]
    have h10 : f (t - x) = f x := by
      have h11 : f x = f (t - x) := h3 x
      linarith
    rw [h7, h10] at h5
    nlinarith

  have h5 : ∀ x, f x = 1 / 2 := by
    intro x
    have h6 := h₁ (x / 2) (x / 2)
    have h7 : (x / 2 : ℝ) + (x / 2 : ℝ) = x := by ring
    rw [h7] at h6
    have h10 : f (t - (x / 2 : ℝ)) = f (x / 2 : ℝ) := by
      have h11 : f (x / 2 : ℝ) = f (t - (x / 2 : ℝ)) := by
        apply h3
      linarith
    rw [h10] at h6
    have h14 : f (x / 2 : ℝ) ^ 2 = 1 / 4 := h4 (x / 2 : ℝ)
    nlinarith

  refine ⟨1 / 2, fun x => h5 x⟩