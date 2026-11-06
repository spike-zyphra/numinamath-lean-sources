import Mathlib

theorem algebra_188090 (x y : ℝ) (h1 : 2*x^2-7*x*y-4*y^2+9*x-18*y+10=0) (h2 : x^2+2*y^2=6) :
    (x=2 ∧ y=1) ∨ (x=-2 ∧ y=-1) ∨ (x=-22/9 ∧ y=-1/9) := by
  have h1' : (2 * x + y + 5) * (x - 4 * y + 2) = 0 := by
    nlinarith
  cases' (mul_eq_zero.1 h1') with h3 h4
  · -- Case where $2x + y + 5 = 0$
    have eq1 : y = -2 * x - 5 := by linarith
    rw [eq1] at h2
    have h3 : (x + 2) * (x + 22 / 9) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h3) with h4 h5
    · -- Case where x = -2
      have hx : x = -2 := by linarith
      have hy : y = -1 := by
        linarith [eq1, hx]
      right
      left
      exact ⟨hx, hy⟩
    · -- Case where x = -22/9
      have hx : x = -22 / 9 := by linarith
      have hy : y = -1 / 9 := by
        nlinarith [eq1, hx]
      right
      right
      exact ⟨hx, hy⟩
  · -- Case where $x - 4y + 2 = 0$
    have eq2 : x = 4 * y - 2 := by linarith
    rw [eq2] at h2
    have h4 : (y - 1) * (y + 1 / 9) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 h4) with h5 h6
    · -- Case where y = 1
      have hy : y = 1 := by linarith
      have hx : x = 2 := by
        nlinarith [eq2, hy]
      left
      exact ⟨hx, hy⟩
    · -- Case where y = -1/9
      have hy : y = -1 / 9 := by linarith
      have hx : x = -22 / 9 := by
        nlinarith [eq2, hy]
      right
      right
      exact ⟨hx, hy⟩