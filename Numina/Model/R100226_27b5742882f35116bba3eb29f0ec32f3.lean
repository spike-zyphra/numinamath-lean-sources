import Mathlib

theorem algebra_153704 (m : ℝ) (hm : m < 0) :
    (1 - m, -abs m) ∈ {p | p.1 > 0 ∧ p.2 < 0} := by
  have h1 : abs m = -m := by
    rw [abs_of_neg]
    all_goals linarith
  have hx : (1 - m : ℝ) > 0 := by
    linarith

  have hy : (-abs m : ℝ) < 0 := by
    rw [h1]
    linarith

  constructor
  · exact hx
  · exact hy