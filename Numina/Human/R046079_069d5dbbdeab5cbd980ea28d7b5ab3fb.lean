import Mathlib

/- Let $a, b, c$ be positive real numbers such that $a^{2}+b^{2}+c^{2}+(a+b+c)^{2} \leq 4$.
Prove that  $$ \frac{a b+1}{(a+b)^{2}}+\frac{b c+1}{(b+c)^{2}}+\frac{c a+1}{(c+a)^{2}} \geq 3 $$ -/
theorem inequalities_604332{a b c: ℝ}(apos: 0 < a)(bpos: 0 < b)
  (cpos: 0 < c)(hineq: a^2+b^2+c^2+(a+b+c)^2 ≤ 4):
  (a*b+1)/(a+b)^2 + (b*c+1)/(b+c)^2 + (c*a+1)/(c+a)^2 ≥ 3 := by
  -- the given condition is a^2+b^2+c^2+ab+bc+ca ≤ 2
  replace hineq: a^2+b^2+c^2+a*b+b*c+c*a ≤ 2 := by nlinarith [hineq]
  -- we show ∑ (ab+1)/(a+b)^2 ≥ 3 by proving 2 ∑ (ab+1)/(a+b)^2 ≥ 6
  suffices h: (2*a*b+2)/(a+b)^2 + (2*b*c+2)/(b+c)^2 +
    (2*c*a+2)/(c+a)^2 ≥ 6 by
    have: (2*a*b+2)/(a+b)^2 + (2*b*c+2)/(b+c)^2 + (2*c*a+2)/(c+a)^2 =
      2 * ((a*b+1)/(a+b)^2 + (b*c+1)/(b+c)^2 + (c*a+1)/(c+a)^2) := by ring
    rw [this] at h; linarith [h]
  -- using the given condition, we prove (2ab+2)/(a+b)^2 ≥ 1 + (c+a)(c+b)/(a+b)^2
  have ineq1{x y z: ℝ}(h: x^2+y^2+z^2+x*y+y*z+z*x ≤ 2)
    (xpos: 0 < x)(ypos: 0 < y):
    (2*x*y+2)/(x+y)^2 ≥ 1 + (z+x)*(z+y)/(x+y)^2 := by
    have hh: 0 < (x+y)^2 := by nlinarith [xpos, ypos]
    calc
    (2*x*y+2)/(x+y)^2 ≥ (2*x*y + (x^2+y^2+z^2+x*y+y*z+z*x))/(x+y)^2 := by
      apply (div_le_div_iff_of_pos_right hh).mpr (by linarith [h])
    _ = ((x+y)^2+(z+x)*(z+y))/(x+y)^2 := by ring
    _ = _ := by field_simp [hh.ne']
  -- it suffices to show ∑ (c+a)(c+b)/(a+b)^2 ≥ 3
  suffices (c+a)*(c+b)/(a+b)^2 + (a+b)*(a+c)/(b+c)^2 +
    (b+c)*(b+a)/(c+a)^2 ≥ 3 by
    -- use the inequality we prove just now.
    have h1: (2*a*b+2)/(a+b)^2 ≥ 1 + (c+a)*(c+b)/(a+b)^2 := by
      apply ineq1 hineq apos bpos
    have h2: (2*b*c+2)/(b+c)^2 ≥ 1 + (a+b)*(a+c)/(b+c)^2 := by
      apply ineq1 ?_ bpos cpos
      apply le_trans (le_of_eq (by ring)) hineq
    have h3: (2*c*a+2)/(c+a)^2 ≥ 1 + (b+c)*(b+a)/(c+a)^2 := by
      apply ineq1 ?_ cpos apos
      apply le_trans (le_of_eq (by ring)) hineq
    linarith [h1, h2, h3]
  -- we prove this inequality holds using AM-GM
  have lemma_amgm{x y z: ℝ}(xpos: 0 < x)(ypos: 0 < y)
    (zpos: 0 < z): x+y+z ≥ 3 * (x*y*z)^(1/3:ℝ) := by
    have xnng := le_of_lt xpos
    have ynng := le_of_lt ypos
    have znng := le_of_lt zpos
    suffices x/3 + y/3 + z/3 ≥ x^(1/3:ℝ) * y^(1/3:ℝ) * z^(1/3:ℝ) by
      have h: x+y+z = 3 * (x/3 + y/3 + z/3) := by ring
      rw [Real.mul_rpow (mul_nonneg xnng ynng) znng]
      rw [Real.mul_rpow xnng ynng, h]
      apply (mul_le_mul_iff_of_pos_left (by norm_num)).mpr this
    have h1: 0 ≤ (1/3:ℝ) := by norm_num
    have h2: (1/3:ℝ)+1/3+1/3 = 1 := by ring
    have := Real.geom_mean_le_arith_mean3_weighted h1 h1 h1
      xnng ynng znng h2
    apply le_trans this (le_of_eq (by ring))
  -- apply AM-GM
  have h1: (c+a)*(c+b)/(a+b)^2 + (a+b)*(a+c)/(b+c)^2 +
    (b+c)*(b+a)/(c+a)^2 ≥ 3 * (((c+a)*(c+b)/(a+b)^2) *
    ((a+b)*(a+c)/(b+c)^2) * ((b+c)*(b+a)/(c+a)^2))^(1/3:ℝ) := by
    apply lemma_amgm ?_ ?_ ?_
    all_goals
      apply div_pos
      <;> nlinarith [apos, bpos, cpos]
  -- right side of h1 is 3
  have h2: ((c+a)*(c+b)/(a+b)^2) * ((a+b)*(a+c)/(b+c)^2) *
    ((b+c)*(b+a)/(c+a)^2) = 1 := by
    have hh1: (a+b)^2 > 0 := by nlinarith [apos, bpos]
    have hh2: (b+c)^2 > 0 := by nlinarith [bpos, cpos]
    have hh3: (c+a)^2 > 0 := by nlinarith [cpos, apos]
    field_simp [hh1.ne', hh2.ne', hh3.ne']
    ring
  -- done
  rw [h2] at h1
  apply le_trans ?_ h1
  simp