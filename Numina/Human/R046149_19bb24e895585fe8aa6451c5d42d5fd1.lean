import Mathlib

/- 4.6.35 $\stackrel{\star \star}{\star}$ In triangle $ABC$, the side lengths $a, b, c$ satisfy $a+b+c=1$. Prove that:

$$

5\left(a^{2}+b^{2}+c^{2}\right)+18 a b c \geqslant \frac{7}{3} .

$$
 -/
theorem inequalities_143592
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c < a + b ∧ b < a + c ∧ a < b + c) (hsum : a + b + c = 1) :
    5 * (a ^ 2 + b ^ 2 + c ^ 2) + 18 * a * b * c ≥ 7 / 3 := by
  -- first relate a^2+b^2+c^2 to (ab+bc+ca)
  have h1 : a^2 + b^2 + c^2 = 1 - 2 * (a * b + b * c + c * a) := by
    rw [show (1 : ℝ) = 1^2 by ring, ← hsum]
    ring
  -- now change goal to a product based format where we'll be able to use amgm and rewrite rhs as the sum
  suffices (5/9 - a) * (5/9 - b) * (5/9 - c) ≤ 8/27^2 by linarith
  rw [show (8/27^2 : ℝ) = 1/27 * (3 * 5 / 9 - 1)^3 by norm_num]
  rw [show 3 * 5/9 - 1 = (5/9 - a) + (5/9 - b) + (5/9 - c) by linarith]
  -- prove a variant of amgm on 3 variable
  have amgm3 (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
      x * y * z ≤ 1/27 * (x + y + z)^3 := by
    have : (0:ℝ) ≤ 1/3 := by norm_num
    have := Real.geom_mean_le_arith_mean3_weighted this this this hx hy hz (by norm_num)
    have := (Odd.strictMono_pow (show Odd 3 by decide)).monotone this
    convert this
    . rw [← Real.rpow_natCast, Real.mul_rpow (by positivity) (by positivity),
        Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul (by positivity),
        ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity)]
      simp
    . ring
  -- now just apply, due to triaangle inequality terms are nonnegative
  apply amgm3 <;> linarith