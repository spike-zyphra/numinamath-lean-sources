import Mathlib


/-- 5. Let $a, b, c$ be the sides of a triangle. Prove the inequality
$$ \frac{a^{3}}{c^{3}}+\frac{b^{3}}{c^{3}}+\frac{3 a b}{c^{2}}>1.$$ -/
theorem inequalities_109998 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b)
  (hc : 0 < c) (h : a + b > c) (_ : a + c > b) (_ : b + c > a) :
    a^3 / c^3 + b^3 / c^3 + 3 * a * b / c^2 > 1 := by
  -- Rewrite the inequality to equivalent form $a^3 + b^3 +3abc > c^3$.
  field_simp
  rw[lt_div_iff₀ (by positivity), one_mul]
  -- From the triangle inequality, it follows that $a+b>c>0$.
  have h_save := h
  convert_to c ^ 3 * c ^ 2 < (a ^ 3 + b ^ 3 + 3 * a * b * c) * c ^ 2
  · ring
  · rw[mul_lt_mul_right (by positivity)]
    have : a^2 - a * b + b ^2 > 0 := by
      convert_to (a-b)^2 + a * b > 0
      · ring
      · positivity
    -- Multiply both sides of the inequality by the positive number a^2 - ab + b^2 (it equals 0 only when a = b = 0)
    -- (a+b)(a^2-ab+b^2) > c(a^2-ab+b^2).
    rw[gt_iff_lt, ← mul_lt_mul_right this,
    -- Add 3abc to both sides of the inequality
    -- (a+b)(a^2-ab+b^2) +3abc > c(a^2-ab+b^2) + 3abc.
       ← add_lt_add_iff_right (3 * a * b * c)] at h
    -- Transform to a^3+b^3 + 3abc > c(a^2-ab +b^2 + 3ab),
    convert_to c * (a^2 - a * b + b^2 + 3 * a * b) < a^3 + b^3 + 3 * a * b * c at h
    · ring
    · ring
    -- further to c(a+b)^2 < a^3 + b^3 + 3abc.
    convert_to c * (a+b)^2 < a^3 + b^3 + 3 * a * b * c at h
    · ring
    trans c * (a + b)^2
    -- Consider that c(a+b)^2 > c^3.
    · convert_to c * c^2 < _
      · ring
      · gcongr
    -- We get a^3+b^3+3abc > c(a+b)^2 > c^3.
    · assumption