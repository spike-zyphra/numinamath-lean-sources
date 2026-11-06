import Mathlib

theorem algebra_277640 (x y z : ℕ) (h₀ : x = y) (h₁ : y = z)
    (h₂ : 220 * x + 250 * y + 330 * z = 36000) :
    x + y + z = 135 := by 
  have h3 : x = y := h₀
  have h4 : y = z := h₁
  omega