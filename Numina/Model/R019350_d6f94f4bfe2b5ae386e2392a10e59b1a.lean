import Mathlib

theorem algebra_161332 {x y : ℝ} (h1 : 3*x-y-3*x*y=-1) (h2 : 9*x^2*y^2+9*x^2+y^2-6*x*y=13) :
    (x=-2/3 ∧ y=1) ∨ (x=1 ∧ y=1) ∨ (x=-1/3 ∧ y=-3) ∨ (x=-1/3 ∧ y=2) := by
  have h3 : (3 * x + 1) * (1 - y) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h3) with h4 h5
  · -- Case $3x + 1 = 0$
    have hx : x = -1/3 := by
      linarith
    rw [hx] at h2
    have hy : (y + 3) * (y - 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp hy) with hy1 hy2
    · -- Case $y + 3 = 0$
      right
      right
      left
      constructor
      · linarith
      · linarith
    · -- Case $y - 2 = 0$
      right
      right
      right
      constructor
      · linarith
      · linarith
  · -- Case $1 - y = 0$
    have hy : y = 1 := by
      linarith
    rw [hy] at h2
    have h6 : (x - 1) * (3 * x + 2) = 0 := by
      nlinarith
    cases' (mul_eq_zero.mp h6) with h7 h8
    · -- Case $x - 1 = 0$
      right
      left
      constructor
      · linarith
      · linarith
    · -- Case $3x + 2 = 0$
      left
      constructor
      · linarith
      · linarith