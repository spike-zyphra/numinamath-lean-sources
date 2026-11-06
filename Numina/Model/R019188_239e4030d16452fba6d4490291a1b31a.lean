import Mathlib

theorem algebra_165978 (x y : ℝ) :
    (2*x^2-3*x*y+y^2=3 ∧ x^2+2*x*y-2*y^2=6) ↔
    (x=2 ∧ y=1) ∨ (x=-2 ∧ y=-1) := by
  constructor
  · -- (∧) direction: both equations hold implies the solutions
    rintro ⟨h1, h2⟩
    -- Now, we have original equation 1 and the difference equation.
    have eq3 : x^2 - 5 * x * y + 3 * y^2 + 3 = 0 := by
      nlinarith 
    -- Now we need to solve equation 1 and equation sub.
    have h5 : (x - 2) * (x + 2) = 0 := by 
      nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), sq_nonneg (x + 2), sq_nonneg (y + 1), sq_nonneg (y - x), sq_nonneg (y + x), sq_nonneg (x * y)]
    cases' (mul_eq_zero.mp h5) with h6 h7
    · -- x = 2
      have hx2 : x = 2 := by linarith 
      have hy1 : y = 1 := by
        nlinarith [sq_nonneg (x - 2), sq_nonneg (y - 1), h1, h2]
      left 
      exact ⟨hx2, hy1⟩ 
    · -- x = -2 
      have hx2 : x = -2 := by linarith 
      have hy1 : y = -1 := by
        nlinarith [sq_nonneg (x + 2), sq_nonneg (y + 1), h1, h2]
      right 
      exact ⟨hx2, hy1⟩ 
  · -- (↔) direction: solutions satisfy both equations
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · -- (2, 1)
      constructor <;> norm_num 
    · -- (-2, -1)
      constructor <;> norm_num