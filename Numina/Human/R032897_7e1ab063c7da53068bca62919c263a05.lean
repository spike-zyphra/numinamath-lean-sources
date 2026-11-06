import Mathlib

/-
Let $a,b, c > 0$ and $abc = 1$. Prove that $\frac{a - 1}{c}+\frac{c - 1}{b}+\frac{b - 1}{a} \ge 0$
-/
theorem inequalities_70890 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) :
    (a - 1) / c + (c - 1) / b + (b - 1) / a ≥ 0 := by
  
  -- Rewrite the habc to h1
  have h1 : a * b * c = 1 := habc

  -- Simplify the expression using field_simp considering positivity constraints of abc, thus it could be the dominator.
  have pos_abc : 0 < a * b * c := by nlinarith [ha, hb, hc]

  have h2 : (a - 1) / c + (c - 1) / b + (b - 1) / a ≥ 0 := by

    -- Clear fractions in the inequality by multiplying through by common denominator, which is positive due to abc > 0
    have h : (a - 1) / c + (c - 1) / b + (b - 1) / a = 
      (a^2 * b + c^2 * a + b^2 * c - a * b - a * c - b * c) / (a * b * c) := by
        field_simp [hc.ne.symm, hb.ne.symm, ha.ne.symm]
        ring

    rw [h]
    have h3 : a^2 * b + c^2 * a + b^2 * c - a * b - a * c - b * c ≥ 0 := by
      -- Use non-negativity properties of squares. Exploiting symmetry and square terms will always be >= 0
      nlinarith [sq_nonneg (a - 1), sq_nonneg (b - 1), sq_nonneg (c - 1),
        sq_nonneg (a * b - 1), sq_nonneg (b * c - 1), sq_nonneg (c * a - 1),
        h1, mul_pos ha hb, mul_pos hb hc, mul_pos ha hc]
    
    -- The numerator being non-negative and equal division due to abc=1 implies original expression is also non-negative
    have h4 : (a^2 * b + c^2 * a + b^2 * c - a * b - a * c - b * c) / (a * b * c) ≥ 0 := by
      apply div_nonneg
      · linarith
      · nlinarith [pos_abc]

    linarith
  linarith [h2]