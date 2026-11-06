import Mathlib

/-- Given non-zero real numbers \(a, b, c\) satisfy:
\[
a + b + c = 0, \quad a^{4} + b^{4} + c^{4} = 128.
\]
Find all possible values of \(ab + bc + ca\). -/
theorem algebra_4036 (a b c:ℝ)(ha: a ≠ 0)(hb: b ≠ 0)(hc: c ≠ 0)
(h1: a + b + c = 0)(h2: a^4 + b^4 + c^4 = 128):a*b+b*c+c*a=-8:= by
-- expand and simplify $(a+b+c)^2$.
have h3:(a + b + c)^2=a^2+b^2+c^2+2*(a*b+b*c+c*a):= by ring
rw[h1] at h3
simp at h3
-- simplify the equation $(a+b+c)*(a^3+b^3+c^3)-(a^4 + b^4 + c^4)$.
have h4:(a+b+c)*(a^3+b^3+c^3)-(a^4 + b^4 + c^4)=(a*(b^3+c^3)+b*(a^3+c^3)+c*(a^3+b^3)):= by ring_nf
rw[h1,h2] at h4
simp at h4
-- get the equation $(a * b + b * c + c * a) = -(a ^ 2 + b ^ 2 + c ^ 2)/2$, so we get $a * b + b * c + c * a \leq 0$.
have h5:(a * b + b * c + c * a) = -(a ^ 2 + b ^ 2 + c ^ 2)/2:= by linarith
rw[h5]
field_simp
ring_nf
have h6:a * (b ^ 3 + c ^ 3) + b * (a ^ 3 + c ^ 3) + c * (a ^ 3 + b ^ 3) = (a*b+b*c+c*a)*(a ^ 2 + b ^ 2 + c ^ 2)-(a + b + c)*a*b*c:= by ring_nf
rw [h6] at h4
rw[h1] at h4
simp at h4
rw[h5] at h4
field_simp at h4
have h7:((a ^ 2 + b ^ 2 + c ^ 2)/16)^2 = 1:= by linarith
let C := (a ^ 2 + b ^ 2 + c ^ 2)/16
have h8:C^2=1:= by dsimp[C]; exact h7
simp at h8
have h9: C > 0 := by dsimp[C];positivity
have h10: C = 1 := by cases h8;assumption;linarith
dsimp[C] at h10
linarith
