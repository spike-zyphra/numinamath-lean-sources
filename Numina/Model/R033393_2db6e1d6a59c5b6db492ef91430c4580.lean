import Mathlib

theorem algebra_226869 (a b c : ℝ) (ha : a ≠ 0)
    (h1 : ∀ x, a * x ^ 2 + b * x + c = a * x + b → x = -1)
    (h2 : ∀ x, a * x ^ 2 + b * x + c = b * x + c → x = 1)
    (h3 : ∀ x, a * x ^ 2 + b * x + c = c * x + a → x = 2)
    (h4 : ∀ x, a * x ^ 2 + b * x + c = b * x + a → x = -2)
    (h5 : ∀ x, a * x ^ 2 + b * x + c = c * x + b → x = 3)
    (h6 : ∀ x, a * x ^ 2 + b * x + c = a * x + c → x = 4) :
    1 ≤ c / a ∧ c / a ≤ 5 := by 
  have h7 := h2 0 (by linarith)
  have h8 : (0 : ℝ) = 1 := by 
    linarith 
  linarith