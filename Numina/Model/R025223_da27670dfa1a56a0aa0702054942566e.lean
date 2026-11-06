import Mathlib

open Real
open scoped BigOperators

theorem algebra_20986 {p : ℝ} (hp : p > 0) (V F A B : ℝ × ℝ)
  (hV : V = (0, p / 2)) (hF : F = (0, p / 2 - 1)) (hA : A ∈ {(x, y) | y = p * x ^ 2})
  (hB : B ∈ {(x, y) | y = p * x ^ 2}) (hAB : A ≠ B) :
  cos (arccos (-3 / 5)) = -3 / 5 := by 
  have h1 : -1 ≤ (-3 / 5 : ℝ) ∧ (-3 / 5 : ℝ) ≤ 1 := by 
    constructor
    · norm_num
    · norm_num
  have h2 : cos (arccos (-3 / 5 : ℝ)) = -3 / 5 := by 
    rw [cos_arccos]
    all_goals linarith
  exact h2