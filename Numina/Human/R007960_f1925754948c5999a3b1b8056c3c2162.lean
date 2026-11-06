import Mathlib

/- The first and ninth terms of an arithmetic sequence are $\frac23$ and $\frac45$, respectively. What is the fifth term? -/
theorem algebra_21566 (a d : ℚ) (h₀ : a = 2 / 3)
    (h₂ : a + 8 * d = 4 / 5) : a + 4 * d = 11 / 15 := by
  rw [h₀] at h₂ ⊢
  linarith