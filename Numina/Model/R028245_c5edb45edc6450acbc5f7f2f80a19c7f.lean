import Mathlib

theorem algebra_161390 {f : ℚ → ℚ} (hf : ∀ x, 0 < x → 0 < f x)
    (h : ∀ x, f x + f (1 / x) = 1) (h' : ∀ x, f (2 * x) = 2 * f (f x)) :
    f (1 / 3) = 1 / 4 := by
  have h1 : f 1 = 1 / 2 := by
    have h11 := h 1
    norm_num at h11 
    linarith
  have eq3 : f (1 / 2 : ℚ) = 1 / 3 := by 
    have eq1 := h' 1
    norm_num [h1] at eq1 
    have eq2 := h 2
    norm_num at eq2
    linarith
  have eq7 := h' (1 / 2 : ℚ)
  norm_num [eq3] at eq7 
  linarith [h1, eq7]