import Mathlib

theorem algebra_308679 {f : ℝ → ℝ} (h : ∀ x, f x + (x - 2) * f 1 + 3 * f 0 = x ^ 3 + 2) :
    f = fun x => x ^ 3 - x + 1 := by
  have eq1 := h 0
  have eq2 := h 1
  have h1 : f 0 = 1 := by
    norm_num at eq1 eq2
    linarith
  have h2 : f 1 = 1 := by
    norm_num at eq1 eq2
    linarith [h1]
  funext x
  have eq5 := h x
  simp [h1, h2] at eq5 ⊢
  linarith