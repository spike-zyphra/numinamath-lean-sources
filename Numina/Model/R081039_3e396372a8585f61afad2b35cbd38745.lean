import Mathlib

theorem algebra_302941 {a b c : ℝ} (h₀ : 2*a+13*b+3*c=90) (h₁ : 3*a+9*b+c=72) :
    (3*b+c)/(a+2*b) = 1 := by
  have h2 : a + 2 * b = 18 := by
    linarith [h₀, h₁]
  have h3 : 3 * b + c = 18 := by
    linarith [h₀, h₁]
  have h4 : 3 * b + c = a + 2 * b := by
    linarith [h2, h3]
  have h5 : a + 2 * b ≠ 0 := by
    linarith [h2]
  field_simp [h5]
  linarith [h4]