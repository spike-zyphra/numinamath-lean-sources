import Mathlib

/- Five runners together complete a $100$-mile endurance race by running separate, non-overlapping portions of the course.  Runner B's portion is $1.5$ times the length of Runner A's portion.  The combined portion for Runners C and D is twice the length of the combined portion for Runners A and B.  Runner E then runs the last $10$ miles of the race.  How many miles did Runner B run? -/
theorem algebra_20972 (a b c d e : ℝ)
    (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e)
    (h₁ : b = 1.5 * a)
    (h₂ : c + d = 2 * (a + b))
    (h₃ : e = 10)
    (h₄ : a + b + c + d + e = 100) :
    b = 18 := by 
  norm_num at h₁ h₂ h₃ h₄
  linarith