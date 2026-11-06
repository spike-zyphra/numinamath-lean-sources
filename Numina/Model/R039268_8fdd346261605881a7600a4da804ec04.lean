import Mathlib

theorem algebra_236703 (f : ℚ → ℚ) (hf : ∀ x, 0 < x → 0 < f x)
    (h1 : ∀ x, f (1 / x) = f x) (h2 : ∀ x, (1 + 1 / x) * f x = f (x + 1)) :
    ∀ x, 0 < x → f x = x.den := by
  intro x hx
  have eq1 := h2 (-1)
  norm_num at eq1 
  have eq2 := h2 0
  norm_num at eq2
  have h3 : 0 < f 1 := by 
    apply hf 1 
    norm_num
  have h4 : (0 : ℚ) < f 0 := by
    linarith 
  linarith [h4, eq1]