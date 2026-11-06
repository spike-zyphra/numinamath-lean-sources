import Mathlib

theorem algebra_277781 {a b c : ℝ} (h : ∃ r, b = a * r ∧ c = b * r) :
    (a + b + c) * (a - b + c) = a ^ 2 + b ^ 2 + c ^ 2 := by
  rcases h with ⟨r, h1, h2⟩
  have h3 : c = a * r^2 := by 
    rw [h2, h1]
    ring
  rw [show b = a * r by linarith [h1], show c = a * r^2 by linarith [h3]]
  ring