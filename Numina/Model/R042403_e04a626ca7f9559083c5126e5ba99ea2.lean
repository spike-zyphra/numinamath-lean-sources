import Mathlib

open Real

theorem algebra_201324 {f g : ℝ → ℝ}
    (h₁ : ∀ x > 0, f (logb 3 x) = logb 3 (9 / x^4) / (logb (1/3) x - logb √3 x))
    (h₂ : ∀ x > 0, (f ∘ g) x = exp x)
    (hpos : ∀ x, g x > 0 ∧ 4 - 3 * rexp x ≠ 0) :
    g (log 2) = -1 := by 
  have h3 := hpos (log (4 / 3))
  have h4 : (4 - 3 * rexp (log (4 / 3))) = 0 := by
    have h5 : rexp (log (4 / 3)) = (4 / 3 : ℝ) := by
      rw [Real.exp_log]
      all_goals norm_num
    rw [h5]
    norm_num
  have h5 := h3.2 
  contradiction