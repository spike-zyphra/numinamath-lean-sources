import Mathlib

/-Let $X$ be a natural number such that $X \ge 2$.
In a certain base $b$, the square of the number represented by two digits $X, X$
(that is, the number $Xb+X$) is the number represented by the three digits $(X^2+1)$, $(X^2-2)$,
and $X^2$ (that is, the number $(X^2+1)b^2 + (X^2-2)b + X^2$).
Show that $b = X^2+2$.-/

theorem number_theory_638047 (X b: ℤ) (hb: 0 < b)
  (h2: (X * b + X) ^ 2 = (X ^ 2 + 1) * b ^ 2 + (X ^ 2 - 2) * b + X ^ 2): b = X ^ 2 + 2 := by

  replace h2: (X * b + X) ^ 2 - ((X ^ 2 + 1) * b ^ 2 + (X ^ 2 - 2) * b + X ^ 2) = 0 := by
    rw [h2]
    ring
  ring_nf at h2
  rw [show X ^ 2 * b + (b * 2 - b ^ 2) = b * (X ^ 2 + 2 - b) by ring] at h2
  simp [hb] at h2
  omega
