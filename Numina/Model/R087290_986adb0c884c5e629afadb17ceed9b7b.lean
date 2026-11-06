import Mathlib

theorem algebra_7876
    (p q : ℝ)
    (h₀ : 0 < p)
    (h₁ : 0 < q)
    (h₂ : p < q) :
    max (max (max (max ((p + 3 * q) / 4) ((p + 2 * q) / 3)) ((p + q) / 2)) ((2 * p + q) / 3)) ((3 * p + q) / 4) = ((p + 3 * q) / 4) := by 
  have h1 : (p + 3 * q) / 4 > (p + 2 * q) / 3 := by 
    linarith
  have h2 : (p + 3 * q) / 4 > (p + q) / 2 := by 
    linarith
  have h3 : (p + 3 * q) / 4 > (2 * p + q) / 3 := by 
    linarith
  have h4 : (p + 3 * q) / 4 > (3 * p + q) / 4 := by 
    linarith
  simp [max_eq_left_of_lt, h1, h2, h3, h4]
  all_goals linarith