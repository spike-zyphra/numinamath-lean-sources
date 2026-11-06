import Mathlib

theorem algebra_252422 {a b c d : ℝ} (h : ∃ r, b = a * r ∧ c = b * r ∧ d = c * r) :
    (a - c) ^ 2 + (b - c) ^ 2 + (b - d) ^ 2 - (a - d) ^ 2 = 0 := by
  rcases h with ⟨r, h1, h2, h3⟩
  have h4 : c = a * r ^ 2 := by 
    rw [h2, h1]
    ring
  have h5 : d = a * r ^ 3 := by 
    rw [h3, h4]
    ring
  rw [show c = a * r ^ 2 by linarith [h4], show b = a * r by linarith [h1], show d = a * r ^ 3 by linarith [h5]]
  ring