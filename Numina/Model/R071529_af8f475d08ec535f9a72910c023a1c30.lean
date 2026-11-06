import Mathlib

theorem algebra_140103 {f : ℝ → ℝ} (hodd : ∀ x, f (-x) = -f x)
    (hfpos : ∀ x > 0, f x = x ^ 2 + Real.sin x) :
    ∀ x < 0, f x = -x ^ 2 + Real.sin x := by 
  intro x hx
  have h1 : -x > 0 := by linarith
  have h2 : f (-x) = (-x) ^ 2 + Real.sin (-x) := hfpos (-x) h1
  have h3 : Real.sin (-x) = - Real.sin x := by 
    rw [Real.sin_neg]
  rw [h3] at h2
  have h4 : f (-x) = x ^ 2 - Real.sin x := by
    have h5 : (-x) ^ 2 = x ^ 2 := by ring
    linarith [h2, h5]
    all_goals linarith [h2, h5]
  have h5 : f (-x) = -f x := hodd x
  linarith [h4, h5]
  all_goals linarith [h4, h5]