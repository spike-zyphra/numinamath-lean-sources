import Mathlib

theorem algebra_138155 (x : ℝ) (hx : 0.35 * 160 + 0.1 * x = 0.2 * 160 + 0.2 * x) :
    0.15 * 160 = 0.1 * x ∧ x = 240 := by 
  have h1 : x = 240 := by
    norm_num at hx
    linarith
  have h2 : 0.15 * 160 = 0.1 * x := by
    rw [h1]
    norm_num
  constructor
  · -- We need to prove 0.15 * 160 = 0.1 * x
    exact h2
  · -- We need to prove x = 240
    exact h1
  all_goals
    try norm_num
    all_goals
      try linarith