import Mathlib

/- Solve for $a$: $3a-7(3-a)=5$. Express your answer as a common fraction in simplest form. -/
theorem algebra_19678 {a : ℝ} (ha : 3 * a - 7 * (3 - a) = 5) :
    a = 13 / 5 := by 
  nlinarith