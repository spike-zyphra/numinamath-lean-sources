import Mathlib

/- Soient $a, b, c>0$ tels que $a^{2}+b^{2}+c^{2}+(a+b+c)^{2} \leqslant 4$. Montrer que

$$
\frac{a b+1}{(a+b)^{2}}+\frac{b c+1}{(b+c)^{2}}+\frac{c a+1}{(c+a)^{2}} \geqslant 3
$$ -/
theorem inequalities_607712 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : a^2 + b^2 + c^2 + (a + b + c)^2 ≤ 4) :
    3 ≤ (a * b + 1) / (a + b)^2 + (b * c + 1) / (b + c)^2 + (c * a + 1) / (c + a)^2 := by
  -- simplify `h`
  have h_quad : a^2 + b^2 + c^2 + a * b + b * c + c * a ≤ 2 := by linear_combination (1/2) * h
  -- homogenize the left-hand side of the inequality to be proven
  have {a b c: ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h_quad : a^2 + b^2 + c^2 + a * b + b * c + c * a ≤ 2) :
    1 / 2 + 1 / 2 * (c + a) * (c + b) / (a + b) ^ 2 ≤ (a * b + 1) / (a + b)^2 := by
    rw [show (a * b + 1) / (a + b)^2 = 1 / 2 * (2 * a * b + 2) / (a + b)^2 by ring_nf]
    apply le_of_sub_nonpos
    calc _ = 1 / 2 * (1 + ((c + a) * (c + b) - (2 * a * b + 2)) / (a + b) ^ 2  ) := by ring_nf
      _ = 1 / 2 * ((a + b) ^ 2 / (a + b) ^ 2 + ((c + a) * (c + b) - (2 * a * b + 2)) / (a + b) ^ 2) := by
        rw [div_self]
        symm
        apply ne_of_lt
        apply sq_pos_of_ne_zero
        linarith
      _ = 1 / 2 * ((a + b) ^ 2 + ((c + a) * (c + b) - (2 * a * b + 2))) / (a + b) ^ 2 := by ring_nf
      _ =(a^2 + b^2 + c^2 + a * b + b * c + c * a - 2) * (1 / 2) / (a + b) ^ 2 := by ring_nf
    apply div_nonpos_of_nonpos_of_nonneg
    apply mul_nonpos_of_nonpos_of_nonneg
    exact sub_nonpos_of_le h_quad
    simp
    exact sq_nonneg (a + b)
  -- add the three inequalities obtained by cyclically permuting the variables
  have : 3 / 2 + 1 / 2 * ((c + a) * (c + b) / (a + b) ^ 2 + (a + b) * (a + c) / (b + c)^2 + (b + c) * (b + a) / (c + a)^2) ≤ (a * b + 1) / (a + b) ^ 2 + (b * c + 1) / (b + c) ^ 2 + (c * a + 1) / (c + a) ^ 2 := by
    linear_combination
      (this ha hb hc h_quad) +
      (this hb hc ha (by apply le_trans' h_quad; apply le_of_eq; ring)) +
      (this hc ha hb (by apply le_trans' h_quad; apply le_of_eq; ring))
  apply le_trans' this

  -- prove each item is positive
  have {a b c:ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) : 0 < (c + a) * (c + b) / (a + b) ^ 2 := by
    apply div_pos
    apply mul_pos
    linarith only [ha, hb, hc]
    linarith only [ha, hb, hc]
    apply sq_pos_of_ne_zero; linarith only [ha, hb, hc]
  have item1_nonneg := le_of_lt <| this ha hb hc
  have item2_nonneg := le_of_lt <| this hb hc ha
  have item3_nonneg := le_of_lt <| this hc ha hb

  -- use AM-GM to prove the inequality
  have : 3 ≤ ((c + a) * (c + b) / (a + b) ^ 2 + (a + b) * (a + c) / (b + c) ^ 2 + (b + c) * (b + a) / (c + a) ^ 2) := by
    have zero_le_one_div_three : (0:ℝ) ≤ 1 / 3 := by norm_num
    have h' := Real.geom_mean_le_arith_mean3_weighted
      zero_le_one_div_three
      zero_le_one_div_three
      zero_le_one_div_three
      item1_nonneg
      item2_nonneg
      item3_nonneg
      (by norm_num)
    rw [
      <-Real.mul_rpow item1_nonneg item2_nonneg,
      <-Real.mul_rpow ((mul_nonneg_iff_left_nonneg_of_pos (this hb hc ha)).2 item1_nonneg) item3_nonneg,
      <-mul_add,
      <-mul_add,
      calc (c + a) * (c + b) / (a + b) ^ 2 * ((a + b) * (a + c) / (b + c) ^ 2) * ((b + c) * (b + a) / (c + a) ^ 2)
        _ = (a + b) ^ 2 / (a + b) ^ 2 * ((b + c) ^ 2 / (b + c) ^ 2) * ((c + a) ^ 2 / (c + a) ^ 2) := by ring_nf
        _ = 1 := by rw [div_self, div_self, div_self]; simp; all_goals {symm; apply ne_of_lt; apply sq_pos_of_ne_zero; linarith only [ha, hb, hc]}
    ] at h'
    simp at h'
    linear_combination 3 * h'

  linear_combination 1 / 2 * this
