import Mathlib

theorem inequalities_237685 (f : ℝ → ℝ)
    (h₁ : ∀ x, f x ≤ x)
    (h₂ : ∀ x y, f (x + y) ≤ f x + f y) :
    ∀ x, f x = x := by

  have h3 : f 0 = 0 := by
    have h4 : f 0 ≤ 0 := by
      apply h₁
    have h5 : 0 ≤ f 0 := by
      have h6 : f (0 + 0) ≤ f 0 + f 0 := by
        apply h₂
      simp at h6
      linarith
    linarith [h4, h5]

  intro x
  have h5 : f (x + (-x)) ≤ f x + f (-x) := by
    apply h₂
  have h7 : f 0 = 0 := h3
  have h8 : f (x + (-x)) = f 0 := by
    simp [show x + (-x) = (0 : ℝ) by ring]
  rw [h8] at h5
  rw [h7] at h5
  have h9 : f (-x) ≤ -x := by
    apply h₁
  have h10 : x ≤ f x := by
    linarith [h5, h9]
  have h11 : f x ≤ x := by
    apply h₁
  linarith [h10, h11]