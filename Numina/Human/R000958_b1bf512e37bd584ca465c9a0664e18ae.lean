import Mathlib

open Real Set
open scoped BigOperators

/-What is the value of $b$ if $5^b + 5^b + 5^b + 5^b + 5^b = 625^{(b-1)}$? Express your answer as a common fraction.-/
theorem algebra_19378 {b : ℝ}
    (h: (5 : ℝ)^b + 5^b + 5^b + 5^b + 5^b = 625^(b-1)) :
    b = 5/3 := by
  -- We can rewrite $5^b + 5^b + 5^b + 5^b + 5^b$ as $5\cdot5^b=5^{(b+1)}$. Since $625=5^4$, we rewrite $625^{(b-1)}$ as $(5^4)^{(b-1)}=5^{4(b-1)}=5^{(4b-4)}$. We now have $5^{(b+1)}=5^{(4b-4)}$, so it must be that the exponents are equal.  $$b+1=4b-4\qquad\Rightarrow 5=3b\qquad\Rightarrow \frac{5}{3}=b$$ The value of $b$ is $\boxed{\frac{5}{3}}$.
  have : (5 : ℝ)^b + 5^b + 5^b + 5^b + 5^b = 5 * 5^b := by linarith
  rw [this, mul_comm, ←(rpow_add_one (by linarith))] at h
  rw [show (625 : ℝ) = 5^(4 : ℝ) by linarith, ←rpow_mul (by linarith)] at h
  have : log (5 ^ (b + 1)) = log (5 ^ (4 * (b - 1))) := by
    rw [h]
  rw [log_rpow (by linarith), log_rpow (by linarith)] at this
  rw [mul_right_cancel_iff_of_pos (by positivity)] at this
  linarith
