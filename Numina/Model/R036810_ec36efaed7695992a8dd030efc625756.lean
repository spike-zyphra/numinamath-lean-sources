import Mathlib

theorem inequalities_597388 (a : Fin 3 → ℝ) (ha : ∀ i, 0 < a i)
    (hsum : ∑ i, a i = 1) :
    ∏ i, ((1 + a i) / (1 - a i)) ≥ 2 ^ 3 := by
  have h1 : a 0 + a 1 + a 2 = 1 := by
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at hsum 
    linarith 
  have ha0 : 0 < a 0 := ha 0 
  have ha1 : 0 < a 1 := ha 1 
  have ha2 : 0 < a 2 := ha 2 
  have ha3 : a 0 < 1 := by 
    nlinarith 
  have ha4 : a 1 < 1 := by
    nlinarith 
  have ha5 : a 2 < 1 := by
    nlinarith
  have eq1' : (∏ i, ((1 + a i) / (1 - a i))) ≥ (8 : ℝ) := by 
    have eq1 : (∏ i, ((1 + a i) / (1 - a i))) = 
            ((1 + a 0) * (1 + a 1) * (1 + a 2) ) / ((1 - a 0) * (1 - a 1) * (1 - a 2)) := by 
      simp [Finset.prod_fin_eq_prod_range, Finset.prod_range_succ]
      <;> field_simp [(show 1 - a 0 ≠ 0 by nlinarith [h1, ha0, ha1, ha2]), 
                (show 1 - a 1 ≠ 0 by nlinarith [h1, ha0, ha1, ha2]), 
                (show 1 - a 2 ≠ 0 by nlinarith [h1, ha0, ha1, ha2])
              ]
      <;> ring 
    have h14 : ((1 + a 0) * (1 + a 1) * (1 + a 2) ) / ((1 - a 0) * (1 - a 1) * (1 - a 2) ) ≥ (8 : ℝ) := by
      have hx1 : 0 < 1 - a 0 := by
        nlinarith 
      have hx2 : 0 < 1 - a 1 := by
        nlinarith 
      have hx3 : 0 < 1 - a 2 := by
        nlinarith 
      have h21 : 0 < (1 - a 0 : ℝ) * (1 - a 1 : ℝ) * (1 - a 2 : ℝ) := by 
        positivity 
      have h15 : 0 < (1 - a 0 : ℝ) := by 
        linarith [hx1]
      have h16 : 0 < (1 - a 1 : ℝ) := by 
        linarith [hx2]
      have h17 : 0 < (1 - a 2 : ℝ) := by 
        linarith [hx3]
      have h18 : ((1 + a 0) * (1 + a 1) * (1 + a 2) ) / ((1 - a 0) * (1 - a 1) * (1 - a 2)) - (8 : ℝ) ≥ 0 := by 
        have h19 : ((1 + a 0) * (1 + a 1) * (1 + a 2) ) / ((1 - a 0) * (1 - a 1) * (1 - a 2)) - (8 : ℝ) = 
            ((1 + a 0) * (1 + a 1) * (1 + a 2) - 8 * ((1 - a 0) * (1 - a 1) * (1 - a 2))) / ((1 - a 0) * (1 - a 1) * (1 - a 2)) := by 
          field_simp 
          ring 
        rw [h19]
        have h20 : 0 < (1 - a 0 : ℝ) * (1 - a 1 : ℝ) * (1 - a 2 : ℝ) := by 
          positivity 
        have h21 : ((1 + a 0) * (1 + a 1) * (1 + a 2) - 8 * ((1 - a 0) * (1 - a 1) * (1 - a 2))) ≥ 0 := by
          nlinarith [sq_nonneg (a 0 - a 1), sq_nonneg (a 1 - a 2), sq_nonneg (a 0 - a 2),
                sq_nonneg (a 0 - 1 / 3), sq_nonneg (a 1 - 1 / 3), sq_nonneg (a 2 - 1 / 3),
                mul_pos ha0 ha1, mul_pos ha1 ha2, mul_pos ha0 ha2
              ]
        apply div_nonneg 
        linarith 
        all_goals positivity 
      linarith 
    linarith [eq1, h14] 
  norm_num at eq1' ⊢ 
  linarith [eq1']
  all_goals positivity