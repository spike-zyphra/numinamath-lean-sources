import Mathlib

open Real
open scoped BigOperators

/- Given a triangle with sides of lengths $a,b,c$, prove that $\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b}< 2$. -/
theorem inequalities_66138 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) :
  a / (b + c) + b / (c + a) + c / (a + b) < 2 := by
  have h₁ : a / (b + c) + b / (c + a) + c / (a + b) < 2 := by
    refine' lt_of_sub_pos _
    field_simp
    ring_nf
    nlinarith [mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, h, h', h'']
  exact h₁