import Mathlib

theorem algebra_264717 {f : ℝ → ℝ} (h : ∀ x y, f x + f y = 2 * f ((x + y) / 2) * f ((x - y) / 2))
    (h' : f (Real.pi / 4) = 0) (h'' : ∃ x, f x ≠ 0) (h''' : f 0 > 0) :
    ∀ x, f (x + Real.pi) = f x := by

  -- First, we can solve for $f(0)$.
  -- Using the equation with $x = 0$ and $y = 0$:
  -- $f(0) + f(0) = 2f\left(\frac{0+0}{2}\right)f\left(\frac{0-0}{2}\right)$
  -- $2f(0) = 2f(0)^2$
  -- $f(0) = f(0)^2$
  -- Since $f(0) > 0$, we can divide by $f(0)$ to get $1 = f(0)$.
  have h1 : f 0 = 1 := by
    have eq1 := h 0 0
    norm_num at eq1
    nlinarith

  -- Compute $f\left(\frac{\pi}{2}\right)$.
  -- Using the functional equation with $x = \frac{\pi}{2}$ and $y = 0$:
  -- $f\left(\frac{\pi}{2}\right) + f(0) = 2f\left(\frac{\frac{\pi}{2} + 0}{2}\right)f\left(\frac{\frac{\pi}{2} - 0}{2}\right)$
  -- $f\left(\frac{\pi}{2}\right) + 1 = 2f\left(\frac{\pi}{4}\right)f\left(\frac{\pi/4}\right)$
  -- $f\left(\frac{\pi}{4}\right) = 0$, so $f\left(\frac{\pi/2}\right) + 1 = 2 \cdot 0 \cdot 0 = 0$
  -- Thus $f\left(\frac{\pi}{2}\right) = -1$.
  have h2 : f (Real.pi / 2) = -1 := by
    have eq1 := h (Real.pi / 2) 0
    have eq2 : (Real.pi / 2 + (0 : ℝ)) / 2 = Real.pi / 4 := by ring_nf
    have eq3 : ((Real.pi / 2 : ℝ) - (0 : ℝ)) / 2 = Real.pi / 4 := by ring_nf
    rw [eq2, eq3] at eq1
    rw [h', h1] at eq1
    nlinarith

  -- Show that $f\left(x + \frac{\pi}{2}\right) = -f(x)$
  have h3 : ∀ x, f (x + Real.pi / 2) = - f x := by
    intro x
    have eq1 := h (x + Real.pi / 2) x
    have eq2 : ((x + Real.pi / 2 + x) / 2 : ℝ) = x + Real.pi / 4 := by ring_nf
    have eq3 : ((x + Real.pi / 2 - x) / 2 : ℝ) = Real.pi / 4 := by ring_nf
    rw [eq2, eq3] at eq1
    simp [h'] at eq1
    linarith

  -- Now, apply the functional equation to $x + \pi$ and $x$:
  -- $f(x + \pi) + f(x) = 2f\left(\frac{(x + \pi) + x}{2}\right)f\left(\frac{(x + \pi) - x}{2}\right)$
  -- $f(x + \pi) + f(x) = 2f\left(x + \frac{\pi}{2}\right)f\left(\frac{\pi}{2}\right)$
  -- Since $f\left(\frac{\pi}{2}\right) = -1$, this becomes:
  -- $f(x + \pi) + f(x) = 2 (-1) f\left(x + \frac{\pi}{2}\right)$
  -- $f(x + \pi) + f(x) = -2 f\left(x + \frac{\pi}{2}\right)$
  -- But $f\left(x + \frac{\pi}{2}\right) = -f(x)$, so:
  -- $f(x + \pi) + f(x) = -2 (-f(x))$
  -- $f(x + \pi) + f(x) = 2 f(x)$
  -- So $f(x + \pi) = f(x)$

  intro x
  have eq1 := h (x + Real.pi) x
  have eq2 : ((x + Real.pi + x) / 2 : ℝ) = x + Real.pi / 2 := by ring_nf
  have eq3 : ((x + Real.pi - x) / 2 : ℝ) = Real.pi / 2 := by ring_nf
  rw [eq2, eq3] at eq1
  rw [h2] at eq1
  have eq5 : f (x + Real.pi / 2) = - f x := h3 x
  rw [eq5] at eq1
  linarith