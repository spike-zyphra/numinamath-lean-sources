import Mathlib

theorem inequalities_46280 (a : Fin 3 → ℝ) (ha : ∀ i, 1 < a i)
    (h : ∀ i, a i ^ 2 / (a i - 1) > ∑ j, a j) :
    1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) > 1 := by
  have h1 : a 0 ^ 2 / (a 0 - 1) > a 0 + a 1 + a 2 := by
    specialize h 0
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
    all_goals linarith
  have h2 : a 1 ^ 2 / (a 1 - 1) > a 0 + a 1 + a 2 := by
    specialize h 1
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
    all_goals linarith
  have h3 : a 2 ^ 2 / (a 2 - 1) > a 0 + a 1 + a 2 := by
    specialize h 2
    simp [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ] at h ⊢
    all_goals linarith
  have ha1 : 1 < a 0 := by apply ha 0
  have ha2 : 1 < a 1 := by apply ha 1
  have ha3 : 1 < a 2 := by apply ha 2
  have h4 : a 0 ^ 2 > (a 0 + a 1 + a 2) * (a 0 - 1) := by
    have ha4 : a 0 - 1 > 0 := by linarith [ha1]
    have h1' : a 0 ^ 2 / (a 0 - 1) > a 0 + a 1 + a 2 := h1
    have ha2' : a 0 - 1 > 0 := by linarith [ha1]
    apply (lt_div_iff₀ (by linarith)).mp at h1'
    linarith
  have h5 : a 1 ^ 2 > (a 0 + a 1 + a 2) * (a 1 - 1) := by
    have ha22 : a 1 - 1 > 0 := by linarith [ha2]
    have h2' : a 1 ^ 2 / (a 1 - 1) > a 0 + a 1 + a 2 := h2
    have ha2' : a 1 - 1 > 0 := by linarith [ha2]
    apply (lt_div_iff₀ (by linarith)).mp at h2'
    linarith
  have h6 : a 2 ^ 2 > (a 0 + a 1 + a 2) * (a 2 - 1) := by
    have ha33 : a 2 - 1 > 0 := by linarith [ha3]
    have h3' : a 2 ^ 2 / (a 2 - 1) > a 0 + a 1 + a 2 := h3
    have ha4' : a 2 - 1 > 0 := by linarith [ha3]
    apply (lt_div_iff₀ (by linarith)).mp at h3'
    linarith
  have h7 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 > 0 := by
    have h7 : (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) > (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) := by
      nlinarith [mul_pos (show (0 : ℝ) < a 0 - 1 by linarith) (show (0 : ℝ) < a 1 - 1 by linarith), 
                  mul_pos (show (0 : ℝ) < a 0 - 1 by linarith) (show (0 : ℝ) < a 2 - 1 by linarith),
                  mul_pos (show (0 : ℝ) < a 1 - 1 by linarith) (show (0 : ℝ) < a 2 - 1 by linarith), 
                  mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha2), 
                  mul_pos (sub_pos.mpr ha2) (sub_pos.mpr ha3), 
                  mul_pos (sub_pos.mpr ha3) (sub_pos.mpr ha1), 
                  mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ha1), 
                  mul_pos (sub_pos.mpr ha2) (sub_pos.mpr ha2), 
                  mul_pos (sub_pos.mpr ha3) (sub_pos.mpr ha3)
                ]
    have h8 : ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) ) / ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) - 1 > 0 := by
      have pos1' : 0 < (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) := by
        positivity
      have h10 : ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) ) > (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) := h7
      have h11 : ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) ) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) > 0 := by linarith [h10]
      have h12 : ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) ) / ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) - 1 = ( ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) ) - (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) / ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) := by
        field_simp
        <;> ring
      rw [h12]
      apply div_pos
      linarith
      all_goals positivity
    have h13 : 1 / (a 0 + a 1) + 1 / (a 1 + a 2) + 1 / (a 2 + a 0) - 1 = ( (a 1 + a 2) * (a 2 + a 0) + (a 0 + a 1) * (a 2 + a 0) + (a 0 + a 1) * (a 1 + a 2) ) / ( (a 0 + a 1) * (a 1 + a 2) * (a 2 + a 0) ) - 1 := by
      field_simp
      <;> ring
    linarith [h13, h8]
  linarith