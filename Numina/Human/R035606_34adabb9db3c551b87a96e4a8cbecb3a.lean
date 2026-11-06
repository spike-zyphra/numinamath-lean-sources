import Mathlib

/- If positive reals $a,b,c,d$ satisfy $abcd = 1.$ Prove the following inequality $$1<\frac{b}{ab+b+
1}+\frac{c}{bc+c+1}+\frac{d}{cd+d+1}+\frac{a}{da+a+1}<2.$$ -/
theorem inequalities_33322 (a b c d : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d)
    (h : a * b * c * d = 1) :
    1 < b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) +
        a / (d * a + a + 1) ∧
    b / (a * b + b + 1) + c / (b * c + c + 1) + d / (c * d + d + 1) +
        a / (d * a + a + 1) < 2 := by
  constructor
  · apply lt_of_sub_pos
    field_simp
    -- Applying algebraic rearrangement using the positives and product equal to 1.
    nlinarith [mul_pos ha hb, mul_pos hb hc, mul_pos hc hd, mul_pos hd ha,
      mul_pos (mul_pos ha hb) hc, mul_pos (mul_pos hb hc) hd, mul_pos (mul_pos hc hd) ha,
      mul_pos (mul_pos hd ha) hb]
  · -- As $b + 1 < a * b + b + 1$, we have $b / (a * b + b + 1) < b / (b + 1)$
    have eq1 : b / (a * b + b + 1) < b / (b + 1) := by
      refine div_lt_div_of_pos_left hb ?_ ?_
      linarith
      linarith [Left.mul_pos ha hb]
    -- $c / (b * c + c + 1) < c / (b * c + c) = 1 / (b + 1)$
    have eq2 : c / (b * c + c + 1) < 1 / (b + 1) := by calc
      _ < c / (b * c + c) := by
        refine div_lt_div_of_pos_left hc ?_ ?_
        linarith [Left.mul_pos hb hc]
        linarith
      _ = _ := by
        refine (div_eq_div_iff ?_ ?_).mpr ?_
        linarith [Left.mul_pos hb hc]
        linarith
        ring
    have eq3 : d / (c * d + d + 1) < d / (d + 1) := by
      refine div_lt_div_of_pos_left hd ?_ ?_
      linarith
      linarith [Left.mul_pos hc hd]
    have eq4 : a / (d * a + a + 1) < 1 / (d + 1) := by calc
      _ < a / (d * a + a) := by
        refine div_lt_div_of_pos_left ha ?_ ?_
        linarith [Left.mul_pos hd ha]
        linarith
      _ = _ := by
        refine (div_eq_div_iff ?_ ?_).mpr ?_
        linarith [Left.mul_pos hd ha]
        linarith
        ring
    -- Add the four equations together, we are done.
    calc
    _ < b / (b + 1) + 1 / (b + 1) + d / (d + 1) + 1 / (d + 1) := by linarith
    _ = 2 := by
      field_simp
      ring
