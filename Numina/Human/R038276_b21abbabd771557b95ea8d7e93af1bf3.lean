import Mathlib

/- 6.361 Solve the equation $a x^{3}+b x^{2}+c x+d=0$, if its coefficients $a, b, c, d$ in the given order form a geometric progression with a given common ratio $q$. -/
theorem algebra_195627 {a b c d q : ℝ} (ha : a ≠ 0) (hq : q ≠ 0) (h : b = a * q) (h' : c = b * q) (h'' : d = c * q) (h''' : a * x^3 + b * x^2 + c * x + d = 0) :
    x = -q := by
  -- replace b, c, d in termrs of q
  rw [h'', h', h] at h'''
  -- expression factorizable to a * (x+q) * (x^2+q^2)
  convert_to a * (x + q) * (x^2 + q^2) = 0 at h'''
  . ring
    -- a ≠ 0 given and due to q≠ 0, we have x^2 + q^2 ≠ 0, so x + q = 0
  . have hxq : x^2 + q^2 ≠ 0 := by
      have : x^2 + q^2 > 0 := by positivity
      linarith
    simp [ha, hxq] at h'''
    linarith