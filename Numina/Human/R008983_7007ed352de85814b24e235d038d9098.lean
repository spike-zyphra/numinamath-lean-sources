import Mathlib

/- Mr. Fat needs 20 minutes to eat a pound of cereal, while Mr. Thin needs 30 minutes. If they eat together, how long does it take for them to finish off three pounds of cereal? Express your answer in minutes. -/
theorem algebra_12480 (v₁ v₂ : ℝ) (h₁ : v₁ * 20 = 1) (h₂ : v₂ * 30 = 1) :
    (3 / (v₁ + v₂)) = 36 := by
  replace h₁ : v₁ = 1 / 20 := by linarith
  replace h₂ : v₂ = 1 / 30 := by linarith
  subst_vars
  norm_num
