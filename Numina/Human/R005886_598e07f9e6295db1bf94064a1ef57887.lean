import Mathlib

/- Real numbers $x$ and $y$ satisfy the following equations:

$$
\begin{aligned}
x & =\log _{10}\left(10^{y-1}+1\right)-1 \\
y & =\log _{10}\left(10^{x}+1\right)-1
\end{aligned}
$$

Compute $10^{x-y}$.-/
theorem algebra_610506 (x y : ℝ) (hx : x = Real.logb 10 ((10 : ℝ) ^ (y - 1) + 1) - 1) (hy : y = Real.logb 10 ((10 : ℝ) ^ x + 1) - 1) : (10 : ℝ) ^ (x - y) = 101 / 110 := by
  -- Simplify the equations hx and hy.
  replace hx := congr_arg ((10 : ℝ) ^ ·) hx
  replace hy := congr_arg ((10 : ℝ) ^ ·) hy
  simp at hx hy
  rw [Real.rpow_sub (by norm_num), Real.rpow_logb (by norm_num) (by norm_num) (by positivity), add_div] at hx hy
  rw [Real.rpow_sub (by norm_num)] at hx ⊢
  -- Let a = 10^x and b = 10^y.
  let a := (10 : ℝ) ^ x
  let b := (10 : ℝ) ^ y
  rw [show (10 : ℝ) ^ x = a by rfl, show (10 : ℝ) ^ y = b by rfl] at hx hy ⊢
  -- Simplify hx and hy.
  field_simp at hx hy
  norm_num at hx hy
  -- Substitute hy into hx.
  rw [hy] at hx
  -- Show that a = 101 / 999.
  have ha : a = 101 / 999 := by
    linarith only [hx]
  -- Show that b = 110 / 999.
  have hb : b = 110 / 999 := by
    linarith only [hx, hy]
  -- Show that a / b = 101 / 110 as desired.
  norm_num [ha, hb]
