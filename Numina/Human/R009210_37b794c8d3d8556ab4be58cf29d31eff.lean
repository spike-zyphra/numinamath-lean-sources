import Mathlib

/- A freshly-painted circular emblem on a football field is completely covered by the smallest possible square tarp. The tarp covers an area of 196 square feet. In square feet, what is the area of the circular emblem? Express your answer in terms of $\pi$. -/
theorem algebra_21130 (r : ℝ) (h₀ : r > 0) (h₁ : (2 * r) ^ 2 = 196) :
    π * r ^ 2 = 49 * π := by 
  have h₂ : r ^ 2 = 49 := by nlinarith
  rw [h₂]
  ring