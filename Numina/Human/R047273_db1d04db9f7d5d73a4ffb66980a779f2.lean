import Mathlib

theorem algebra_50657 :
    ¬∃ f g : Polynomial ℝ, ∀ x y : ℝ, x^200 * y^200 + 1 = f.eval x * g.eval y := by 
  intro ⟨f, g, H⟩ 
  have h1 := H 1 0
  have h2 := H 0 0
  have h3 := H 0 1
  have h4 := H 1 1
  nlinarith