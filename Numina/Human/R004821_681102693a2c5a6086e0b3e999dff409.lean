import Mathlib
/- Example 1 Given $x, y, z \in \mathbf{R}^{+}$, and $x y z=1$, prove: $\frac{1}{1+x+y}+\frac{1}{1+y+z}+\frac{1}{1+z+x} \leqslant 1$ -/
theorem inequalities_597186 (x y z : ℝ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (hxyz : x * y * z = 1) :
1 / (1 + x + y) + 1 / (1 + y + z) + 1 / (1 + z + x) ≤ 1:= by
  set a:= x ^ ((1 : ℝ) / 3) with ha
  set b:= y ^ ((1 : ℝ) / 3) with hb
  set c:= z ^ ((1 : ℝ) / 3) with hc
  clear_value a b c
  -- Prove that x, y, z are positive
  have hapos : a > 0:= by subst a ; positivity
  have hbpos : b > 0:= by subst b ; positivity
  have hcpos : c > 0:= by subst c ; positivity
  -- Establish the relationship between x^3 and a
  replace ha : a ^ 3 = x:= by
    rw [show a ^ 3 = a ^ (3 : ℝ) by norm_cast]
    subst a
    rw [←(Real.rpow_mul (by positivity) (1 / 3) 3)]
    simp
  -- Establish the relationship between y^3 and b
  replace hb : b ^ 3 = y:= by
    rw [show b ^ 3 = b ^ (3 : ℝ) by norm_cast]
    subst b
    rw [←(Real.rpow_mul (by positivity) (1 / 3) 3)]
    simp
  -- Establish the relationship between z^3 and c
  replace hc : c ^ 3 = z:= by
    rw [show c ^ 3 = c ^ (3 : ℝ) by norm_cast]
    subst c
    rw [←(Real.rpow_mul (by positivity) (1 / 3) 3)]
    simp
  -- Prove that x*y*z = 1 from the constraint a*b*c = 1
  have h1 : a * b * c = 1:= by
    rw [←ha, ←hb, ←hc] at hxyz
    replace h : (a * b * c - 1) * ((2 * a * b * c + 1) ^ 2 + 3) = 0:= by linarith
    have g1 : (2 * a * b * c + 1) ^ 2 + 3 ≠ 0:= by positivity
    simp [g1] at h
    linarith
  -- Rewrite the expression in terms of x, y, z
  rw [←ha, ←hb, ←hc]
  clear ha hb hc hx hy hz hxyz x y z
  -- Apply inequality: a^3 + b^3 + 1 ≥ a^2*b + a*b^2 + 1
  have g1 : 1 + a ^ 3 + b ^ 3 ≥ 1 + a ^ 2 * b + a * b ^ 2:= by
    suffices (a + b) * (a - b) ^ 2 ≥ 0 by linarith
    positivity
  -- Apply inequality: b^3 + c^3 + 1 ≥ b^2*c + b*c^2 + 1
  have g2 : 1 + b ^ 3 + c ^ 3 ≥ 1 + b ^ 2 * c + b * c ^ 2:= by
    suffices (b + c) * (b - c) ^ 2 ≥ 0 by linarith
    positivity
  -- Apply inequality: c^3 + a^3 + 1 ≥ c^2*a + c*a^2 + 1
  have g3 : 1 + c ^ 3 + a ^ 3 ≥ 1 + c ^ 2 * a + c * a ^ 2:= by
    suffices (c + a) * (c - a) ^ 2 ≥ 0 by linarith
    positivity
  -- Apply the fact that 1/a ≤ 1/b if a ≥ b > 0
  replace g1:= one_div_le_one_div_of_le (by positivity) g1
  replace g2:= one_div_le_one_div_of_le (by positivity) g2
  replace g3:= one_div_le_one_div_of_le (by positivity) g3
  -- Simplify the expressions using the constraint x*y*z = 1
  rw [show 1 / (1 + a ^ 2 * b + a * b ^ 2) = c / (a + b + c) by rw [←h1] ; field_simp ; ring_nf] at g1
  rw [show 1 / (1 + b ^ 2 * c + b * c ^ 2) = a / (a + b + c) by rw [←h1] ; field_simp ; ring_nf] at g2
  rw [show 1 / (1 + c ^ 2 * a + c * a ^ 2) = b / (a + b + c) by rw [←h1] ; field_simp ; ring_nf] at g3
  -- Prove that the sum of the three fractions equals 1
  have g4 : c / (a + b + c) + a / (a + b + c) + b / (a + b + c) = 1:= by field_simp ; ring_nf
  -- Complete the proof using linear arithmetic
  linarith
