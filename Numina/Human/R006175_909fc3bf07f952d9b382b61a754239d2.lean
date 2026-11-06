import Mathlib
/- Given $p$, $q$ are real numbers, and $q>3$, satisfying ${{p}^{2}}q+12p-12\leqslant 3{{p}^{2}}+4pq-4q$, then the value of $\frac{p-2}{q-3}$ is ___          ___ .-/
theorem algebra_628882 (p q : ℝ) (hq : 3 < q) (h : p^2 * q + 12 * p - 12 ≤ 3 * p^2 + 4 * p * q - 4 * q) :
    (p - 2) / (q - 3) = 0 := by
  have h1 : (q - 3) * (p - 2) ^ 2 ≤ 0:= by linarith
  have h2 : (p - 2) ^ 2 = 0:= by nlinarith
  have hp : p = 2:= by nlinarith
  rw [hp]
  field_simp [sub_ne_zero.mpr (by linarith : q ≠ 3)]