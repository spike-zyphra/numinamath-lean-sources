import Mathlib

/- 6. Given real numbers $a, b, c$ satisfy $a+b+c=6$, $ab+bc+ca=5$, $abc=1$, then $\frac{1}{a^{3}}+\frac{1}{b^{3}}+\frac{1}{c^{3}}=$ $\qquad$ . -/
theorem algebra_165479 (a b c : ℝ) (h₀ : a + b + c = 6) (h₁ : a * b + b * c + c * a = 5)
    (h₂ : a * b * c = 1) :
    1 / a^3 + 1 / b^3 + 1 / c^3 = 38 := by
  -- let's first show that the numbers are not 0
  have ha: a ≠ 0 := by by_contra h; rw [h] at h₂; simp at h₂
  have hb: b ≠ 0 := by by_contra h; rw [h] at h₂; simp at h₂
  have hc: c ≠ 0 := by by_contra h; rw [h] at h₂; simp at h₂
  -- let's put everything to the common denominator
  field_simp
  -- and simplify
  rw [show a^3*b^3*c^3=(a*b*c)^3 by ring_nf, h₂, one_pow, mul_one, add_mul]
  -- it's well known that x^3+y^3+z^3 = (x+y+z)^3-3*(x+y+z)*(xy+yz+zx)+3xyz
  rw [show b ^ 3 * c ^ 3 + a ^ 3 * c ^ 3 + a ^ 3 * b ^ 3 = (a*b)^3+(b*c)^3+(c*a)^3 by ring_nf,
      show (a*b)^3+(b*c)^3+(c*a)^3 = (a*b+b*c+c*a)^3-3*(a*b+b*c+c*a)*(a*b*b*c+b*c*c*a+c*a*a*b)+3*a*b*b*c*c*a by ring_nf,
      h₁, show 3*a*b*b*c*c*a = 3*(a*b*c)^2 by ring_nf, h₂, one_pow, mul_one,
      show a * b * b * c + b * c * c * a + c * a * a * b = a * b * c * (a+b+c) by ring_nf, h₀, h₂
  ]
  -- we are left with a simple calculation
  norm_num