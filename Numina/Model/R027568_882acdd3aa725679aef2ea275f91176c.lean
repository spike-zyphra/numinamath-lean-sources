import Mathlib

theorem algebra_110784 (a b c x y z : ℝ)
    (h₀ : a^2 + b^2 + c^2 = 4) (h₁ : x^2 + y^2 + z^2 = 9) :
    a * x + b * y + c * z ∈ Set.Icc (-6) 6 := by
  have h2 : (a * x + b * y + c * z) ^ 2 ≤ 36 := by
    nlinarith [sq_nonneg (a * y - b * x), sq_nonneg (b * z - c * y), sq_nonneg (c * x - a * z),
              sq_nonneg (a * x + b * y + c * z), sq_nonneg (a * z - c * x), sq_nonneg (b * x - a * y), 
              sq_nonneg (c * y - b * z), h₀, h₁, 
              mul_nonneg (show 0 ≤ (a^2 + b^2 + c^2 : ℝ) by linarith [h₀]) 
                           (show 0 ≤ (x^2 + y^2 + z^2 : ℝ) by linarith [h₁])]
  have h3 : -6 ≤ a * x + b * y + c * z := by
    nlinarith [h2, sq_nonneg (a * x + b * y + c * z)]
  have h4 : a * x + b * y + c * z ≤ 6 := by
    nlinarith [h2, sq_nonneg (a * x + b * y + c * z)]
  constructor
  · -- Show that -6 ≤ a * x + b * y + c * z
    linarith
  · -- Show that a * x + b * y + c * z ≤ 6
    linarith