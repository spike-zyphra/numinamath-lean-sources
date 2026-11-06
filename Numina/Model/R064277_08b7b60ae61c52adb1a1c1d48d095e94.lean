import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_184314 {f : ℝ → ℝ}
  (hf : f = λ x => sqrt ((x + 2)^2 - 8 * x) / (sqrt x - 2 / sqrt x)) :
  ∀ x, x ∈ Ioo 0 2 → f x = -sqrt x ∧ x > 2 → f x = sqrt x := by
  intro x hx h_contra
  rcases hx with ⟨hx1, hx2⟩
  have h1 : x < 2 := hx2
  have h2 : x > 2 := h_contra.right
  linarith