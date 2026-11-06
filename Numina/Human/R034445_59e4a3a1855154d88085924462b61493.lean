import Mathlib

/- Let $a, b, c, d$ be strictly positive real numbers. Show that the following inequality is true:


$$

\frac{a}{b}+\frac{b}{c}+\frac{c}{d}+\frac{d}{a} \geqslant 4

$$
 -/
theorem inequalities_126634 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) :
    4 ≤ a / b + b / c + c / d + d / a := by
  -- we'll use am-gm on a/b, b/c, c/d, d/a
  have h1 : 0 ≤ (1:ℝ)/4 := by norm_num
  have hab : 0 ≤ a / b := by positivity
  have hbc : 0 ≤ b / c := by positivity
  have hcd : 0 ≤ c / d := by positivity
  have hda : 0 ≤ d / a := by positivity
  have h := Real.geom_mean_le_arith_mean4_weighted h1 h1 h1 h1 hab hbc hcd hda (by norm_num)
  -- a/b * b/c * c/d * d/a = 1, plugging that in, we'll get our inequality
  rw [← Real.mul_rpow (by positivity) (by positivity)] at h
  rw [← Real.mul_rpow (by positivity) (by positivity)] at h
  rw [← Real.mul_rpow (by positivity) (by positivity)] at h
  have habcd : a / b * (b / c) * (c / d) * (d / a) = 1 := by field_simp
  rw [habcd] at h
  simp at h
  linarith