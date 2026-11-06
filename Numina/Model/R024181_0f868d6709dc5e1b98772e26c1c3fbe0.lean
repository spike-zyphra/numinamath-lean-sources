import Mathlib

open Real Set

theorem algebra_4805 {x y : ℝ} (h1 : x^2+3*x*y-3*(x-y)=0) (h2 : x^4+9*y*(x^2+y)-5*x^2=0) :
    (x=0 ∧ y=0) ∨ (x=1 ∧ y=1/3) := by
  have h3 : (x - 0) * (x - 1) = 0 := by
    nlinarith [sq_nonneg (x^2 - 3 * y), sq_nonneg (x - 1), sq_nonneg (y - 1 / 3), sq_nonneg (x^2 - 1), sq_nonneg (y - 0), sq_nonneg (x - y), sq_nonneg (x + 1), sq_nonneg (y + 1 / 3)]
  cases' (mul_eq_zero.1 h3) with h4 h5
  · -- Case $x = 0$
    have hx0 : x = 0 := by linarith
    have hy0 : y = 0 := by
      rw [hx0] at h1
      nlinarith
    left
    exact ⟨hx0, hy0⟩
  · -- Case $x = 1$
    have hx1 : x = 1 := by linarith
    have hy1 : y = 1 / 3 := by
      rw [hx1] at h1
      nlinarith
    right
    exact ⟨hx1, hy1⟩