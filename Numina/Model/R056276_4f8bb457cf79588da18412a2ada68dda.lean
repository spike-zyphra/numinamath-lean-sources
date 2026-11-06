import Mathlib

theorem algebra_308371 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) * f (x - y) = (f x + f y)^2 - 4 * x^2 * f y) :
    ∀ x, f x = 0 ∨ f x = x^2 := by 
  have h1 : f 0 = 0 := by 
    have h1 := h 0 0
    simp at h1 
    nlinarith 
  intro x 
  have h2 := h x x 
  simp [h1] at h2 
  have : f x * (f x - x^2) = 0 := by
    nlinarith [h2]
  cases' (mul_eq_zero.mp this) with hfx hx
  · left
    exact hfx
  · right
    linarith 
  all_goals tauto 
  all_goals nlinarith 
  all_goals norm_num 
  all_goals ring_nf 
  all_goals nlinarith