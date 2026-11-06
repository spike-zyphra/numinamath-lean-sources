import Mathlib

open Real
open scoped BigOperators

theorem inequalities_109902 (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
  (h : a + b > c) (h' : a + c > b) (h'' : b + c > a) (k : ℝ) (hk : a^2 + b^2 = k * c^2) :
  k > 0.5 := by
  have h_eq1 : k = (a^2 + b^2) / c^2 := by
    have hc2_pos : c ^ 2 > 0 := by
      nlinarith [hc]
    field_simp [(show c ≠ 0 by nlinarith [hc, ha, hb, h, h', h''])]
    nlinarith [hk, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc]
  have h3 : k > 0.5 := by
    rw [h_eq1]
    have hc2_pos : c ^ 2 > 0 := by nlinarith [hc]
    
    have h4 : 2 * (a ^ 2 + b ^ 2) > c ^ 2 := by
      nlinarith [sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc, 
                mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, 
                mul_pos (sub_pos.mpr h) (sub_pos.mpr h'), 
                mul_pos (sub_pos.mpr h) (sub_pos.mpr h''), 
                mul_pos (sub_pos.mpr h') (sub_pos.mpr h''), 
                sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)
      ]
    -- Now solving for $\frac{a^2 + b^2}{c^2} > 0.5$
    apply (lt_div_iff₀' (by
      nlinarith [hc]
    )).mpr
    nlinarith [h4, mul_pos ha hb, mul_pos ha hc, mul_pos hb hc, sq_pos_of_pos ha, sq_pos_of_pos hb, sq_pos_of_pos hc
    ]
  linarith [h3]