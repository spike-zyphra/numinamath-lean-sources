import Mathlib

theorem algebra_244254 (x y : ℝ) (h : 2*x^2+3*x*y+y^2=70 ∧ 6*x^2+x*y-y^2=50) :
    (x=3 ∧ y=4) ∨ (x=-3 ∧ y=-4) := by
  rcases h with ⟨h₁, h₂⟩
  have h3 : (x - 3) * (x + 3) = 0 := by
    nlinarith [sq_nonneg (x * y), sq_nonneg (x + y), sq_nonneg (y - 4), sq_nonneg (y + 4), sq_nonneg (x * 2 + y), sq_nonneg (x), sq_nonneg (y)]
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case x = 3
    have hx1 : x = 3 := by linarith
    have hy1 : y = 4 := by 
      nlinarith [h₁, h₂, hx1]
    left 
    exact ⟨hx1, hy1⟩
  · -- Case x = -3
    have hx2 : x = -3 := by linarith
    have hy2 : y = -4 := by 
      nlinarith [h₁, h₂, hx2]
    right 
    exact ⟨hx2, hy2⟩