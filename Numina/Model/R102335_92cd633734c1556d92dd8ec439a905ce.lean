import Mathlib

theorem algebra_130487 {f : ℝ → ℝ} (h : ∀ x y, f (x + y) = f x + f y + 6 * x * y) (h' : f (-1) * f 1 ≥ 9) :
    f (2 / 3) = 4 / 3 := by
  have h0 : f 0 = 0 := by
    have eq1 := h 0 0
    norm_num at eq1 
    linarith
  have h_neg : ∀ x, f (-x) = -f x + 6 * x ^ 2 := by
    intro x
    specialize h x (-x)
    rw [show x + -x = (0 : ℝ) by ring] at h
    rw [h0] at h
    linarith
  have h1 : f 1 = 3 := by
    have h1' : f (-1) = -f 1 + 6 * (1 : ℝ) ^ 2 := h_neg 1
    nlinarith [h', h1']
  have eq1 := h (1 / 3) (2 / 3)
  norm_num at eq1
  have eq2 := h (1 / 3) (1 / 3)
  norm_num at eq2
  nlinarith [h1, eq1, eq2]