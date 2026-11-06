import Mathlib
open Real Set
open scoped BigOperators

/- Given the equation $\left|  x\right|  =ax+1$, if it has both positive and negative roots, then the range of values for $a$ is ___          ___. -/
theorem algebra_8241 (a : ℝ) (h : ∃ x : ℝ, x > 0 ∧ abs x = a * x + 1)
  (h' : ∃ x : ℝ, x < 0 ∧ abs x = a * x + 1) :
  -1 < a ∧ a < 1 := by
  rcases h with ⟨x1, hx1_pos, h1⟩
  rcases h' with ⟨x2, hx2_neg, h2⟩
  have h1_pos : abs x1 = x1 := abs_of_pos hx1_pos
  rw [h1_pos] at h1
  have h_a_lt_1 : a < 1 := by
    nlinarith
  have h2_neg : abs x2 = -x2 := abs_of_neg hx2_neg
  rw [h2_neg] at h2
  have h_a_gt_neg1 : -1 < a := by
    nlinarith
  constructor
  · exact h_a_gt_neg1
  · exact h_a_lt_1