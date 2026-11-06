import Mathlib

/- Let $r$ be a solution to the equation ${{x}^{3}}-x+3=0$, then the monic integer coefficient cubic equation with ${{r}^{2}}$ as a solution is ___          ___. -/
theorem algebra_12567 {r : ℝ} (hr : r^3 - r + 3 = 0) :
    (r^2)^3 - 2 * (r^2)^2 + r^2 - 9 = 0 := by
  have hr1 : r^3 = r - 3 := by linarith
  have hr2 : r^4 = r^2 - 3 * r := by 
    calc 
      r^4 = r * r^3 := by ring
      _ = r * (r - 3) := by rw [hr1]
      _ = r^2 - 3 * r := by ring
  have hr3 : r^6 = r^2 - 6 * r + 9 := by
    calc
      r^6 = (r^3)^2 := by ring
      _ = (r - 3)^2 := by rw [hr1]
      _ = r^2 - 6 * r + 9 := by ring
  calc 
    (r^2)^3 - 2 * (r^2)^2 + r^2 - 9 
        = r^6 - 2 * r^4 + r^2 - 9 := by ring
    _ = (r^2 - 6 * r + 9) - 2 * (r^2 - 3 * r) + r^2 - 9 := by rw [hr3, hr2]
    _ = 0 := by ring