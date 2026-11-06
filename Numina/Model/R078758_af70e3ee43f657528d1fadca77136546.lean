import Mathlib

/- Given ${{x}^{2}}-5x-2019=0$, then the value of $\frac{{{(x-2)}^{3}}-{{(x-1)}^{2}}+1}{x-2}$ is ___          ___. -/
theorem algebra_4200 {x : ℝ} (hx : x^2 - 5 * x - 2019 = 0) (hx1 : x ≠ 2) : ((x - 2)^3 - (x - 1)^2 + 1) / (x - 2) = 2023 := by
  have h1 : x - 2 ≠ 0 := by
    intro h
    apply hx1
    linarith
  have eq1 : (x - 2)^3 - (x - 1)^2 + 1 = (x - 2) * (x^2 - 5 * x + 4) := by
    ring
  rw [eq1]
  field_simp [h1]
  nlinarith