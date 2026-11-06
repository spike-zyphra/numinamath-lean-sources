import Mathlib
open Real
/- 11. Let $\mathrm{f}$ be a function defined on non-zero real numbers such that

$$

\frac{27 \mathrm{f}(-x)}{x}-x^{2} \mathrm{f}\left(\frac{1}{x}\right)=-2 x^{2},

$$

for all $x \neq 0$. Find $\mathrm{f}(3)$. -/
theorem algebra_102997 {f : ℝ → ℝ} (hf : ∀ x ≠ 0, (27 * f (-x)) / x - x ^ 2 * f (1 / x) = -2 * x ^ 2) :
    f 3 = 2 := by
    -- use x = -3 and x = 1/3, then eliminate to conclude
    calc
      f 3 = (9 * (27 * f (- -3) / -3 - (-3)^2 * f (1/ -3)) + (27 * f (-(1/3)) / (1/3) - (1/3)^2 * f (1 / (1/3)))) / (-81-1/9) := by rw [mul_div_right_comm, mul_div_right_comm]; ring_nf
        _ = 2 := by rw [hf (-3) (by linarith), hf (1/3) (by linarith)]; norm_num