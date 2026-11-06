import Mathlib

/- Let $a,$ $b,$ $c$ be distinct real numbers such that
\[\frac{a}{b - c} + \frac{b}{c - a} + \frac{c}{a - b} = 0.\]Find all possible values of
\[\frac{a}{(b - c)^2} + \frac{b}{(c - a)^2} + \frac{c}{(a - b)^2}.\]Enter all the possible values, separated by commas. -/
theorem algebra_10817 {a b c : ℝ} (ha : a ≠ b) (hb : b ≠ c) (hc : a ≠ c)
    (h : a / (b - c) + b / (c - a) + c / (a - b) = 0) :
    a / (b - c)^2 + b / (c - a)^2 + c / (a - b)^2 = 0 := by
  field_simp [sub_ne_zero.2 ha, sub_ne_zero.2 hb, sub_ne_zero.2 hc, sub_ne_zero.2 ha.symm, sub_ne_zero.2 hb.symm, sub_ne_zero.2 hc.symm] at h ⊢
  nlinarith