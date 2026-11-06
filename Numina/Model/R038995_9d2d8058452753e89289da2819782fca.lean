import Mathlib

theorem algebra_188212 {P : Polynomial ℝ} (hP1 : P.eval 1 = 1)
    (hP : ∀ x, P.eval (2 * x) / P.eval (x + 1) = 8 - 56 / (x + 7)) :
    P.eval (-1) = -5 / 21 := by 
  have h1 := hP 0
  norm_num at h1
  have h0 : P.eval 0 = 0 := by
    field_simp [hP1] at h1 
    linarith
  have eq2 := hP (-1)
  norm_num [h0] at eq2
  all_goals
    linarith