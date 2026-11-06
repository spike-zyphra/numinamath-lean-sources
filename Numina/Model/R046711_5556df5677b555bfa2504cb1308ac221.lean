import Mathlib

theorem number_theory_29412 (x y : ℤ) (hx : x > 0) (hy : y > 0)
    (h : 4*x^3+4*x^2*y-15*x*y^2-18*y^3-12*x^2+6*x*y+36*y^2+5*x-10*y=0) :
    ∃ a, x=2*a ∧ y=a ∨ (x, y)=(1, 1) := by
  have h1 : (x - 2 * y) * (2 * x + 3 * y - 1) * (2 * x + 3 * y - 5) = 0 := by
    nlinarith
  cases' (mul_eq_zero.mp h1) with h2 h3
  · cases' (mul_eq_zero.mp h2) with h4 h5
    · -- Case \( x - 2y = 0 \).
      use y
      left
      constructor
      · -- Show \( x = 2y \) (trivial as \( x - 2y = 0 \)).
        linarith
      · -- Show \( y = y \) (trivial).
        linarith
    · -- Case \( 2x + 3y - 1 = 0 \).
      exfalso
      nlinarith [show x ≥ 1 by linarith, show y ≥ 1 by linarith]
  · -- Case \( 2x + 3y - 5 = 0 \).
    have h8 : 2 * x + 3 * y = 5 := by linarith
    have h9 : x ≤ 2 := by
      nlinarith [show y ≥ 1 by linarith]
    have h10 : y ≤ 1 := by
      nlinarith [show x ≥ 1 by linarith]
    have hy1 : y = 1 := by
      omega
    have hx1 : x = 1 := by
      rw [show y = 1 by linarith [hy1]] at h8
      omega
    use 0
    right
    simp [hx1, hy1]