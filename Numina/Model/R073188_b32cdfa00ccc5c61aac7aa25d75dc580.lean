import Mathlib

theorem algebra_10743 {f : ℝ → ℝ} (h : f (-1 + 2) = 3) (hsymm : ∀x, f (-x) = f x) : f (-1) = 3 := by
  have h1 : f 1 = 3 := by
    norm_num at h
    linarith
  have h2 : f (-1) = f 1 := by 
    specialize hsymm 1
    norm_num at hsymm ⊢
    linarith
  rw [h1] at h2
  linarith