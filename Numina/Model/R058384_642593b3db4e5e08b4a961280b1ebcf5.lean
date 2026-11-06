import Mathlib

theorem algebra_130452 (a : ℝ) :
    (∃ x, 10*x^2 + x - a - 11 = 0 ∧ 4*x^2 + (a + 4)*x - 3*a - 8 = 0) ↔
    a = 0 ∨ a = -2 ∨ a = 54 := by
  constructor
  · -- Assume there exists an x satisfying both equations
    rintro ⟨x, ⟨h1, h2⟩⟩
    have eq1 : a = 10 * x^2 + x - 11 := by linarith
    rw [eq1] at h2
    have eq2 : 10 * x^3 - 25 * x^2 - 10 * x + 25 = 0 := by
      nlinarith
    have factored : (x - 1) * (x + 1) * (2 * x - 5) = 0 := by
      nlinarith
    cases' (mul_eq_zero.1 factored) with h3 h4
    cases' (mul_eq_zero.1 h3) with h5 h6
    · -- Case $x - 1 = 0 \imply x = 1$
      have hx1 : x = 1 := by linarith
      have ha1 : a = 0 := by
        rw [hx1] at eq1
        linarith
      left
      exact ha1
    · -- Case $x + 1 = 0 \imply x = -1$
      have hx2 : x = -1 := by linarith
      have ha2 : a = -2 := by
        rw [hx2] at eq1
        linarith
      right
      left
      exact ha2
    · -- Case $2x - 5 = 0 \imply x = 5/2$
      have hx3 : x = 5 / 2 := by linarith
      have ha3 : a = 54 := by
        rw [hx3] at eq1
        nlinarith
      right
      right
      exact ha3
  · -- Assume a ∈ {0, -2, 54}, prove that there exists x satisfying both equations
    rintro (ha | ha | ha)
    · -- a = 0
      use 1
      constructor
      · -- Check first equation
        nlinarith [ha]
      · -- Check second equation
        nlinarith [ha]
    · -- a = -2
      use -1
      constructor
      · -- Check first equation
        nlinarith [ha]
      · -- Check second equation
        nlinarith [ha]
    · -- a = 54
      use 5 / 2
      constructor
      · -- Check first equation
        nlinarith [ha]
      · -- Check second equation
        nlinarith [ha]