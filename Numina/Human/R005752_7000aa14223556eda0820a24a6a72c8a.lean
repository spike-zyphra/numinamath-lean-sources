import Mathlib

/-
Compute $\frac{x}{w}$ if $w \neq 0$ and
$\frac{x+6 y-3 z}{-3 x+4 w}=\frac{-2 y+z}{x-w}=\frac{2}{3}$.
-/
theorem algebra_609735 (w x y z : ℝ)
    (hw : w ≠ 0) (hxw1 : -3*x + 4*w ≠ 0) (hxw2 : x - w ≠ 0)
    (h1 : (x + 6*y - 3*z) / (-3*x + 4*w) = 2 / 3)
    (h2 : (-2*y + z) / (x - w) = 2 / 3)
    : x / w = 2 / 3 := by

  /-
  The crucial observations are:
  $x = (x + 6y - 3z) + 3(-2y + z)$, and
  $w = (-3x + 4w) + 3(x - w)$.
  We can use these to replace $x$ with other terms, and cancel out $w$.
  -/
  have xeq : x = (x + 6*y - 3*z) + 3*(-2*y + z) := by linarith
  have weq : w = (-3*x + 4*w) + 3*(x - w)       := by linarith

  -- Rewriting first assumption to isolate $x + 6y - 3z$:
  have eqn1 : x + 6*y - 3*z = 2/3 * (-3*x + 4*w) :=
    Eq.symm ((fun hc => (eq_mul_inv_iff_mul_eq₀ hc).mp) hxw1 (id (Eq.symm h1)))

  -- Rewriting second assumption to isolate $-2y + z$:
  have eqn2 : -2*y + z = 2/3 * (x - w) :=
    Eq.symm ((fun hc => (eq_mul_inv_iff_mul_eq₀ hc).mp) hxw2 (id (Eq.symm h2)))

  calc x / w
    _ = ((x + 6*y - 3*z) + 3*(-2*y + z)) / w      := by rw [xeq]; field_simp; linarith
    _ = ((2/3 * (-3*x + 4*w)) + 3*(-2*y + z)) / w := by rw [eqn1]
    _ = ((2/3*(-3*x+4*w)) + 3*(2/3*(x-w))) / w    := by rw [eqn2]
    _ = 2/3 * ((-3*x + 4*w) + 3*(x - w)) / w      := by ring
    _ = 2/3 * w / w                               := by ring
    _ = 2/3                                       := mul_div_cancel_right₀ (2 / 3) hw
