import Mathlib

theorem algebra_605012 {P : Polynomial ℝ} (hP : ∀ x ∈ Set.Icc (-1) 1, P.eval (x * Real.sqrt 2) = P.eval (x + Real.sqrt (1 - x ^ 2))) :
    ∃ f : ℝ → ℝ, ∀ x, P.eval x = f (x / Real.sqrt 2) := by
  use λ y => P.eval (y * Real.sqrt 2)
  intro x
  have h1 : ( (x / Real.sqrt 2) * Real.sqrt 2 ) = x := by
    field_simp [Real.sqrt_ne_zero']
    <;> nlinarith [Real.sqrt_pos.mpr (show (0 : ℝ) < 2 by norm_num), Real.sq_sqrt (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)]
  have h_right : (λ y => P.eval (y * Real.sqrt 2)) (x / Real.sqrt 2) = P.eval x := by
    simp [h1]
  linarith [h_right]