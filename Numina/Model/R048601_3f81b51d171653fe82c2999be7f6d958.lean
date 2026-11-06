import Mathlib

theorem algebra_148470 (x : Fin 5 → ℝ) (a : Fin 5 → ℝ)
    (h₀ : a 0 > a 1) (h₁ : a 1 > a 2) (h₂ : a 2 > a 3) (h₃ : a 3 > a 4)
    (h₄ : x 0 + x 1 + x 2 = a 0) (h₅ : x 1 + x 2 + x 3 = a 1)
    (h₆ : x 2 + x 3 + x 4 = a 2) (h₇ : x 3 + x 4 + x 0 = a 3)
    (h₈ : x 4 + x 0 + x 1 = a 4) :
    x 2 > x 0 ∧ x 0 > x 3 ∧ x 3 > x 1 ∧ x 1 > x 4 := by

  -- x_0 - x_3 = a_0 - a_1 > 0 because a_0 > a_1
  have h1 : x 0 > x 3 := by
    linarith
  -- x_2 - x_0 = a_2 - a_3 > 0 because a_2 > a_3
  have h2 : x 2 > x 0 := by
    linarith
  -- x_3 - x_1 = a_3 - a_4 > 0 because a_3 > a_4
  have h3 : x 3 > x 1 := by
    linarith
  -- x_1 - x_4 = a_1 - a_2 > 0 because a_1 > a_2
  have h4 : x 1 > x 4 := by
    linarith
  
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩