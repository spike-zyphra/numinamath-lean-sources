import Mathlib

theorem algebra_270386 {x y z : ℝ} (h1 : abs (x + y) = 1 - z) (h2 : abs (y + z) = 1 - x)
    (h3 : abs (z + x) = 1 - y) :
    x + y + z = 1 ∨ x + y + z = -3 := by

  cases' abs_cases (x + y) with h1p h1n
  · -- Case where $x + y \geq 0$, so $|x + y| = x + y$
    cases' abs_cases (y + z) with h2p h2n
    · -- Case where $y + z \geq 0$, so $|y + z| = y + z$
      cases' abs_cases (z + x) with h3p h3n
      · -- Case where $z + x \geq 0$, so $|z + x| = z + x$
        left
        linarith
      · -- Case where $z + x < 0$, so $|z + x| = -(z + x)$
        left
        linarith
    · -- Case where $y + z < 0$, so $|y + z| = -(y + z)$
      cases' abs_cases (z + x) with h3p h3n
      · -- Case where $z + x \geq 0$, so $|z + x| = z + x$
        left
        linarith
      · -- Case where $z + x < 0$, so $|z + x| = -(z + x)$
        left
        linarith
  · -- Case where $x + y < 0$, so $|x + y| = -(x + y)$
    cases' abs_cases (y + z) with h2p h2n
    · -- Case where $y + z \geq 0$, so $|y + z| = y + z$
      cases' abs_cases (z + x) with h3p h3n
      · -- Case where $z + x \geq 0$, so $|z + x| = z + x$
        left
        linarith
      · -- Case where $z + x < 0$, so $|z + x| = -(z + x)$
        left
        linarith
    · -- Case where $y + z < 0$, so $|y + z| = -(y + z)$
      cases' abs_cases (z + x) with h3p h3n
      · -- Case where $z + x \geq 0$, so $|z + x| = z + x$
        left
        linarith
      · -- Case where $z + x < 0$, so $|z + x| = -(z + x)$
        right
        linarith