import Mathlib

/- Let $x,$ $y,$ $z$ be real numbers, all greater than 3, so that
\[\frac{(x + 2)^2}{y + z - 2} + \frac{(y + 4)^2}{z + x - 4} + \frac{(z + 6)^2}{x + y - 6} = 36.\]Enter the ordered triple $(x,y,z).$ -/
theorem algebra_16266 {x y z : ℝ} (hx : 3 < x) (hy : 3 < y) (hz : 3 < z)
    (h : (x + 2)^2 / (y + z - 2) + (y + 4)^2 / (z + x - 4) + (z + 6)^2 / (x + y - 6) = 36) :
    (x, y, z) = (10, 8, 6) := by
  -- multiply (y+z-2)+(z+x-4)+(x+y-6) to both sides of the equation, then we can use Cauchy-Schwarz inequality. here we write some auxilary lemmas, basically about Cauchy-Schwarz inequality.
  have lemma_sqge{a b x y:ℝ}(ha: 0 < a)(hb: 0 < b):
    b*x^2/a + a*y^2/b ≥ 2*x*y := by
      have h1: b*x^2/a+a*y^2/b = (b*x^2/a+a*y^2/b-2*x*y)+2*x*y := by ring
      have h2: b*x^2/a+a*y^2/b-2*x*y = (√b/√a*x-√a/√b*y)^2 := by
        ring_nf
        have ht1: √a^2 = a := Real.sq_sqrt (le_of_lt ha)
        have ht2: √b^2 = b := Real.sq_sqrt (le_of_lt hb)
        have ht3: x*y*√b*√a*(√a)⁻¹*(√b)⁻¹*2 = x*y*2 := by field_simp
        simp [ht1, ht2, ht3]; ring
      have h3 := sq_nonneg (√b/√a*x-√a/√b*y)
      rw [h1,h2]
      exact le_add_of_nonneg_left h3
  have lemma_sqgt{a b x y:ℝ}(ha: 0 < a)(hb: 0 < b)(hab: x/a ≠ y/b):
    b*x^2/a + a*y^2/b > 2*x*y := by
      have h1: b*x^2/a+a*y^2/b = (b*x^2/a+a*y^2/b-2*x*y)+2*x*y := by ring
      have h2: b*x^2/a+a*y^2/b-2*x*y = (√b/√a*x-√a/√b*y)^2 := by
        ring_nf
        have ht1: √a^2 = a := Real.sq_sqrt (le_of_lt ha)
        have ht2: √b^2 = b := Real.sq_sqrt (le_of_lt hb)
        have ht3: x*y*√b*√a*(√a)⁻¹*(√b)⁻¹*2 = x*y*2 := by field_simp
        simp [ht1, ht2, ht3]; ring
      have h3: 0 < (√b/√a*x-√a/√b*y)^2 := by
        have ht1 := sq_nonneg (√b/√a*x-√a/√b*y)
        have ht2: (√b/√a*x-√a/√b*y)^2 ≠ 0 := by
          have: √b/√a*x-√a/√b*y ≠ 0 := by
            by_contra! hcc
            have nhab: x/a = y/b := by
              have tt1: √b/√a*x = √a/√b*y := by
                rw [← add_zero (√a/√b*y), ← hcc]; ring
              have tt2: x = a*y/b := by
                have: x = (√b/√a) * x / (√b/√a) := by
                  field_simp
                rw [this, tt1]; field_simp
                ring_nf; simp [Real.sq_sqrt (le_of_lt ha), mul_comm]
              rw [tt2]; field_simp; ring
            contradiction
          apply pow_ne_zero 2 this
        exact lt_of_le_of_ne ht1 (id (Ne.symm ht2))
      rw [h1,h2]
      linarith [h3]
  have lemma_c_s_aux_1{a b c x y z:ℝ}(ha: 0 < a)(hb: 0 < b)(hc: 0 < c):
  (a+b+c)*(x^2/a+y^2/b+z^2/c) =
    (x^2+y^2+z^2) + (b*x^2/a+a*y^2/b) + (a*z^2/c+c*x^2/a)
      + (b*z^2/c+c*y^2/b) := calc
    (a+b+c) * (x^2/a+y^2/b+z^2/c) = (x^2+a*y^2/b+a*z^2/c) + (b*x^2/a+y^2+b*z^2/c) + (c*x^2/a+c*y^2/b+z^2) := by
      ring_nf
      rw [mul_comm a (x^2), mul_comm b (y^2), mul_comm c (z^2)]
      rw [mul_assoc (x^2), mul_assoc (y^2), mul_assoc (z^2)]
      simp [ha.ne', hb.ne', hc.ne']; ring
    _ = (x^2+y^2+z^2) + (b*x^2/a+a*y^2/b) + (a*z^2/c+c*x^2/a)
      + (b*z^2/c+c*y^2/b) := by ring
  have lemma_c_s_aux_2(x y z:ℝ):
    (x+y+z)^2 = (x^2+y^2+z^2) + 2*x*y + 2*z*x + 2*z*y := by ring
  have lemma_c_s_ineq{a b c x y z:ℝ}(ha: 0 < a)(hb: 0 < b)(hc: 0 < c):
    (a+b+c)*(x^2/a+y^2/b+z^2/c) ≥ (x+y+z)^2 := calc
    (a+b+c) * (x^2/a+y^2/b+z^2/c) =
      (x^2+y^2+z^2) + (b*x^2/a+a*y^2/b) + (a*z^2/c+c*x^2/a)
      + (b*z^2/c+c*y^2/b) := lemma_c_s_aux_1 ha hb hc
    _ ≥ (x^2+y^2+z^2) + 2*x*y + 2*z*x + 2*z*y := by
      have ht1: (b*x^2/a+a*y^2/b) ≥ 2*x*y := by
        apply lemma_sqge ha hb
      have ht2: (a*z^2/c+c*x^2/a) ≥ 2*z*x := by
        apply lemma_sqge hc ha
      have ht3: (b*z^2/c+c*y^2/b) ≥ 2*z*y := by
        apply lemma_sqge hc hb
      linarith [ht1, ht2, ht3]
    _ = (x+y+z)^2 := by ring
  -- for cauchy-schwarz inequality, two sides are equal when those three parts are equal.
  have lemma_eq_of_c_s_eq{a b c x y z:ℝ}(ha: 0 < a)(hb: 0 < b)(hc: 0 < c):
    (a+b+c)*(x^2/a+y^2/b+z^2/c) = (x+y+z)^2 → x/a = y/b ∧ y/b = z/c := by
      by_contra! h
      have ht1 := h.left
      have ht2 := h.right
      have ht3: (a*z^2/c+c*x^2/a) ≥ 2*z*x := by
        apply lemma_sqge hc ha
      have nht1: (a+b+c)*(x^2/a+y^2/b+z^2/c) > (x+y+z)^2 := by
        rw [lemma_c_s_aux_1 ha hb hc, lemma_c_s_aux_2 x y z]
        by_cases hab: x/a = y/b
        · have hbc := ht2 hab
          have ht4: (b*x^2/a+a*y^2/b) ≥ 2*x*y := by
            apply lemma_sqge ha hb
          have ht5: (b*z^2/c+c*y^2/b) > 2*z*y := by
            apply lemma_sqgt hc hb hbc.symm
          linarith [ht3, ht4, ht5]
        · push_neg at hab
          have ht4: (b*x^2/a+a*y^2/b) > 2*x*y := by
            apply lemma_sqgt ha hb hab
          have ht5: (b*z^2/c+c*y^2/b) ≥ 2*z*y := by
            apply lemma_sqge hc hb
          linarith [ht3, ht4, ht5]
      linarith [nht1, ht1]
  -- multiply (y+z-2)+(z+x-4)+(x+y-6) to both sides
  have h1: ((y+z-2)+(z+x-4)+(x+y-6)) *
    ((x+2)^2/(y+z-2) + (y+4)^2/(z+x-4) + (z+6)^2/(x+y-6)) =
      ((y+z-2)+(z+x-4)+(x+y-6)) * 36 := by rw [h]
  have ineq1: 36 * (2*(x+y+z)-12) ≥ (x+y+z+12)^2 := by
    have ht1: 36*(2*(x+y+z)-12) =
      ((y+z-2)+(z+x-4)+(x+y-6))*36 := by ring
    have ht2: (x+y+z+12)^2 = ((x+2)+(y+4)+(z+6))^2 := by ring
    rw [ht1, ht2, ← h1]
    -- to apply cauchy-schwarz inequality, we should argue y+z-2,z+x-4,x+y-6 are all positive. they hold because x,y,z all > 3.
    have ht3: 0 < y+z-2 := by linarith [hy, hz]
    have ht4: 0 < z+x-4 := by linarith [hz, hx]
    have ht5: 0 < x+y-6 := by linarith [hx, hy]
    apply lemma_c_s_ineq ht3 ht4 ht5
  -- see x+y+z as a whole
  let s := x+y+z
  have s_def: s = x+y+z := rfl
  rw [← s_def] at ineq1
  -- now we have 36(2s-12) ≥ (s+12)^2, and we can simplify it to s^2-48s+576 ≤ 0, which is (s-24)^2 ≤ 0, therefore s=24.
  have h2: x+y+z = 24 := by
    have ht1: (s+12)^2-36*(2*s-12) ≤ 0 := by
      exact tsub_nonpos.mpr ineq1
    -- (s+12)^2-36(2s-12) = s^2+24s+144-72s+36x12 = s^2-48s + (144+36x12)
    -- 36x12=360+72=432, and 432+144 = 576
    have ht2: (s+12)^2-36*(2*s-12) = s^2-48*s+576 := by ring
    -- factorization, s^2-48s+576 = (s-24)^2
    have ht3: s^2-48*s+576 = (s-24)^2 := by ring
    rw [ht2, ht3] at ht1
    have ht4 := sq_nonneg (s-24)
    have ht5: (s-24)^2 = 0 := le_antisymm ht1 ht4
    have ht6: s-24 = 0 := pow_eq_zero ht5
    rw [← add_zero 24, ← ht6, s_def]; ring
  -- s=24 also shows the cauchy_schwarz inequality must take equal sign.
  have h3: ((y+z-2)+(z+x-4)+(x+y-6))*((x+2)^2/(y+z-2) + (y+4)^2/(z+x-4) + (z+6)^2/(x+y-6)) = ((x+2)+(y+4)+(z+6))^2 := by
    have ht1: ((y+z-2)+(z+x-4)+(x+y-6)) = 2*s-12 := by
      rw [s_def]; ring
    have ht2: (x+2)+(y+4)+(z+6) = s+12 := by
      rw [s_def]; ring
    rw [h, ht1, ht2, s_def, h2]; ring
  --therefore we claim those three parts are equal.
  have h4: (x+2)/(22-x) = (y+4)/(20-y) ∧ (y+4)/(20-y) = (z+6)/(18-z):= by
    have ht1: 0 < y+z-2 := by linarith [hy, hz]
    have ht2: 0 < z+x-4 := by linarith [hz, hx]
    have ht3: 0 < x+y-6 := by linarith [hx, hy]
    have ht4: 22-x = y+z-2 := by
      have: (22:ℝ) = 24-2 := by norm_num
      rw [this, ← h2]; ring
    have ht5: 20-y = z+x-4 := by
      have: (20:ℝ) = 24-4 := by norm_num
      rw [this, ← h2]; ring
    have ht6: 18-z = x+y-6 := by
      have: (18:ℝ) = 24 - 6 := by norm_num
      rw [this, ← h2]; ring
    rw [ht4, ht5, ht6]
    apply lemma_eq_of_c_s_eq ht1 ht2 ht3 h3
  -- if a/b = c/d, then a/b = c/d = (a+c)/(b+d)
  have lemma_div_add{a b c d:ℝ}(hb:b ≠ 0)(hd: d ≠ 0)(hbd: b+d ≠ 0):
    a/b = c/d → a/b = (a+c)/(b+d) := by
    intro h
    have h1: a*d = b*c := by
      have: a = a/b * b := by
        symm; exact div_mul_cancel₀ a hb
      rw [this, h]; ring_nf; simp [hd]
    field_simp; ring_nf; simp [h1]
  -- if a/b = c/d = e/f, then a/b = (a+c+e)/(b+d+f)
  have lemma_div_add_three{a b c d e f:ℝ}(hb:b ≠ 0)(hd: d ≠ 0)(hf:f ≠ 0)(hbd: b+d ≠ 0)(hbdf: b+d+f ≠ 0):
    a/b = c/d ∧ c/d = e/f → a/b = (a+c+e)/(b+d+f) := by
      intro h
      have ht1: a/b = (a+c)/(b+d) := by
        apply lemma_div_add hb hd hbd h.left
      rw [ht1]
      have ht2: (a+c)/(b+d) = e/f := by
        rw [← ht1, h.left, h.right]
      apply lemma_div_add hbd hf hbdf ht2
  -- now we can show (x+2)/(22-x)=(y+4)/(20-y)=(z+6)/(18-z)=(x+y+z+12)/(60-(x+y+z))=1, and solve x,y,z.
  have h5: 22-x > 0 := by
    have ht1: (22:ℝ) = 24-2 := by norm_num
    rw [ht1, ← h2]; linarith [hx, hy, hz]
  have h6: 20-y > 0 := by
    have ht1: (20:ℝ) = 24-4 := by norm_num
    rw [ht1, ← h2]; linarith [hx, hy, hz]
  have h7: 18-z > 0 := by
    have ht1: (18:ℝ) = 24-6 := by norm_num
    rw [ht1, ← h2]; linarith [hx, hy, hz]
  have eqx: (x+2)/(22-x) = 1 := by
    have h8: ((x+2)+(y+4)+(z+6))/((22-x)+(20-y)+(18-z)) = 1 := by
      have ht1: (x+2)+(y+4)+(z+6) = (x+y+z) + 12 := by ring
      have ht2: (22-x)+(20-y)+(18-z) = 60 - (x+y+z) := by ring
      rw [ht1, ht2, h2]; norm_num
    rw [← h8]
    apply lemma_div_add_three h5.ne' h6.ne' h7.ne'
      (by linarith [h5,h6]) (by linarith [h5, h6, h7]) h4
  have eqy: (y+4)/(20-y) = 1 := by
    have h8: ((y+4)+(x+2)+(z+6))/((20-y)+(22-x)+(18-z)) = 1 := by
      have ht1: (y+4)+(x+2)+(z+6) = (x+y+z) + 12 := by ring
      have ht2: (20-y)+(22-x)+(18-z) = 60 - (x+y+z) := by ring
      rw [ht1, ht2, h2]; norm_num
    rw [← h8]
    apply lemma_div_add_three h6.ne' h5.ne' h7.ne'
      (by linarith [h6,h5]) (by linarith [h6,h5,h7])
    rw [h4.left, ← h4.right]; simp
  have eqz: (z+6)/(18-z) = 1 := by
    have h8: ((z+6)+(x+2)+(y+4))/((18-z)+(22-x)+(20-y)) = 1 := by
      have ht1: (z+6)+(x+2)+(y+4) = (x+y+z) + 12 := by ring
      have ht2: (18-z)+(22-x)+(20-y) = 60 - (x+y+z) := by ring
      rw [ht1, ht2, h2]; norm_num
    rw [← h8]
    apply lemma_div_add_three h7.ne' h5.ne' h6.ne'
      (by linarith [h7,h5]) (by linarith [h7,h5,h6])
    rw [← h4.right, h4.left]; simp
  -- from eqx,eqy,eqz, we can solve x,y,z.
  have xeq10: x = 10 := by
    have ht1: x+2 = 22-x := by
      rw [← mul_one (22-x), ← eqx]; field_simp
    linarith [ht1]
  have yeq8: y = 8 := by
    have ht1:y+4 = 20-y := by
      rw [← mul_one (20-y), ← eqy]; field_simp
    linarith [ht1]
  have zeq6: z = 6 := by
    have ht1: z+6 = 18-z := by
      rw [← mul_one (18-z), ← eqz]; field_simp
    linarith [ht1]
  rw [xeq10, yeq8, zeq6]