import Mathlib

/-
Given the complex number $z=a^2+a-2+(a^2-3a+2)i$ is a pure imaginary number, find the real number $a$
-/
theorem algebra_8984
    {a : ℝ}
    (z : ℂ)
    (hz : z = a ^ 2 + a - 2 + (a ^ 2 - 3 * a + 2) * Complex.I)
    (h : z.re = 0 ∧ z.im ≠ 0) : a = -2 := by

  -- the real part of z
  have r1 : z.re = a ^ 2 + a - 2 := by
    simp [hz, pow_two]

  -- the imaginary part of z
  have r2 : z.im = a ^ 2 - 3 * a + 2 := by
    simp [hz, pow_two]

  rw [r1, r2] at h
  obtain ⟨h1, h2⟩ := h

  -- Solving the equation $a^2+a-2=0$, we obtain $a=-2$.
  rw [show a ^ 2 + a - 2 = (a + 2) * (a - 1) by ring] at h1
  rcases mul_eq_zero.mp h1
  . linarith
  . rw [show a = 1 by linarith] at h2
    norm_num at h2

