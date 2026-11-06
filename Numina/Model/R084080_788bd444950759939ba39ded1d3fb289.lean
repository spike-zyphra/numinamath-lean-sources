import Mathlib

theorem algebra_204220 {a b d : ℝ} (ha : 70 + a = 120) (hb : b + 700 = 1400) (hd : 430 - d = 370) :
    a = 50 ∧ b = 700 ∧ d = 60 := by 
  constructor
  · -- Solving for a
    linarith
  constructor
  · -- Solving for b
    linarith
  · -- Solving for d
    linarith