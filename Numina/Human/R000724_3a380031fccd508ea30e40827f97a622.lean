import Mathlib
/-Let $a,$ $b,$ and $c$ be nonzero real numbers such that $a + b + c = 0.$  Simplify
\[\frac{1}{b^2 + c^2 - a^2} + \frac{1}{a^2 + c^2 - b^2} + \frac{1}{a^2 + b^2 - c^2}.\]-/
theorem algebra_14300 (a b c : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h : a + b + c = 0) :
    1 / (b ^ 2 + c ^ 2 - a ^ 2) + 1 / (a ^ 2 + c ^ 2 - b ^ 2) +
    1 / (a ^ 2 + b ^ 2 - c ^ 2) = 0 := by
    --From the equation $a + b + c = 0,$ $a = -b - c
  have ha2: a = -b - c :=  by
    have e := congrArg (fun t  => t - b - c) h ;beta_reduce at e
    rw [show a + b + c  - b - c = a  by ring_nf] at e ; rw[e]
    simp
    --so\[\frac{1}{b^2 + c^2 - a^2} = \frac{1}{b^2 + c^2 - (b + c)^2} = \frac{1}{-2bc} = -\frac{1}{2bc}.\]
  have ha3 : 1 / (b ^ 2 + c ^ 2 - a ^ 2) = 1 / (b ^ 2 + c ^ 2 -( b + c )^ 2) := by
      rw [ha2] ; simp; ring_nf
  have ha4 := calc
    1 / (b ^ 2 + c ^ 2 - a ^ 2) = 1 / (b ^ 2 + c ^ 2 -( b + c )^ 2) := ha3
    _ = 1 /(-2* b * c) := by simp ;ring_nf
    _ = - 1 / (2 * b * c):= by ring_nf
  --Similarly,\[\frac{1}{a^2 + c^2 - b^2} = -\frac{1}{2ac} \quad \text{and} \quad \frac{1}{a^2 + b^2 - c^2} = -\frac{1}{2ab},\]
  have hb2: b = -a - c :=  by
    have e := congrArg (fun t  => t - a - c) h ;beta_reduce at e
    rw [show a + b + c  - a - c = b  by ring_nf] at e ; rw[e]
    simp
  have hb3 : 1 / (a ^ 2 + c ^ 2 - b ^ 2) = 1 / (a ^ 2 + c ^ 2 -( a + c )^ 2) := by
      rw [hb2] ; simp; ring_nf
  have hb4 := calc
    1 / (a ^ 2 + c ^ 2 - b ^ 2) = 1 / (a ^ 2 + c ^ 2 -( a + c )^ 2) := hb3
    _ = 1 /(-2* a * c) := by simp ;ring_nf
    _ = - 1 / (2 * a * c):= by ring_nf

  have hc2: c = -a - b :=  by
    have e := congrArg (fun t  => t - a - b) h ;beta_reduce at e
    rw [show a + b + c  - a - b = c  by ring_nf] at e ; rw[e]
    simp
  have hc3 : 1 / (a ^ 2 + b ^ 2 - c ^ 2) = 1 / (a ^ 2 + b ^ 2 -( a + b )^ 2) := by
      rw [hc2] ; simp; ring_nf
  have hc4 := calc
    1 / (a ^ 2 + b ^ 2 - c ^ 2) = 1 / (a ^ 2 + b ^ 2 -( a + b )^ 2) := hc3
    _ = 1 /(-2* a * b) := by simp ;ring_nf
    _ = - 1 / (2 * a * b):= by ring_nf
  --so\frac{1}{b^2 + c^2 - a^2} + \frac{1}{a^2 + c^2 - b^2} + \frac{1}{a^2 + b^2 - c^2} &= -\frac{1}{2bc} - \frac{1}{2ac} - \frac{1}{2ab} \\&= -\frac{a + b + c}{2abc} = \boxed{0}.
  rw[ha4,hb4,hc4]
  have he : -1 / (2 * b * c) + -1 / (2 * a * c) + -1 / (2 * a * b) = -( a + b + c) / (2* a * b * c) := by
    have ha5: -1 /(2 * b * c)= -( a / a )/(2 * b * c) := by
      rw[div_self];exact ha
    have hb5: -1 /(2 * a * c)= -( b / b )/(2 * a * c) := by
      rw[div_self];exact hb
    have hc5: -1 /(2 * a * b)= -( c / c )/(2 * a * b) := by
      rw[div_self];exact hc
    rw[ha5,hb5,hc5];ring_nf
  rw[he,h];simp
