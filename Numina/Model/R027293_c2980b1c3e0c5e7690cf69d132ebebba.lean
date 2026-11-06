import Mathlib

open Real Set
open scoped BigOperators

theorem algebra_246793 :
  IsGreatest {t : ℝ | ∃ x y, t = ((12*x^2 + 27*y^2 + 12*x + 36*y + 29) / (4*x^2 + 9*y^2 + 4*x + 12*y + 9))^2} (49/4) := by
  constructor
  · -- Show that 49/4 is achievable, with x = -1/2, y = -2/3
    use -1/2, -2/3
    norm_num
  · -- Show that any element in the set is ≤ 49/4
    intro t ht
    rcases ht with ⟨x, y, ht⟩ 
    have h_eq : 4*x^2 + 9*y^2 + 4*x + 12*y + 9 = 4*(x + 1/2)^2 + 9*(y + 2/3)^2 + 4 := by
      ring
    have h_pos : 4*(x + 1/2)^2 + 9*(y + 2/3)^2 ≥ 0 := by
      nlinarith [sq_nonneg (x + 1/2), sq_nonneg (y + 2/3)]
    have h_ge : 4*x^2 + 9*y^2 + 4*x + 12*y + 9 ≥ 4 := by 
      nlinarith [h_eq, h_pos]
    have h_pos_denom : 4*x^2 + 9*y^2 + 4*x + 12*y + 9 > 0 := by
      nlinarith [sq_nonneg (x + 1/2), sq_nonneg (y + 2/3), h_eq]
    have h_eq_num : 12*x^2 + 27*y^2 + 12*x + 36*y + 29 = 3*(4*x^2 + 9*y^2 + 4*x + 12*y + 9) + 2 := by
      ring
    have h_bound : (12*x^2 + 27*y^2 + 12*x + 36*y + 29) / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) = 3 + 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) := by 
      have eq3 : (12*x^2 + 27*y^2 + 12*x + 36*y + 29) = 3* (4*x^2 + 9*y^2 + 4*x + 12*y + 9) + 2 := by
        linarith
      have h1 : 4*x^2 + 9*y^2 + 4*x + 12*y + 9 > 0 := h_pos_denom
      rw [eq3]
      field_simp [h1]
    rw [h_bound] at ht
    have h_le : 3 + 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) ≤ 7 / 2 := by
      have h2 : 4*x^2 + 9*y^2 + 4*x + 12*y + 9 ≥ 4 := h_ge
      have h3 : 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) ≤ 1 / 2 := by
        apply (div_le_div_iff (by positivity) (by positivity)).mpr
        nlinarith [h2]
      linarith
    have h_sq : (3 + 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9)) ^ 2 ≤ 49 / 4 := by
      have h5_pos : (4*x^2 + 9*y^2 + 4*x + 12*y + 9) > 0 := h_pos_denom
      have h5_le : 3 + 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) ≤ 7 / 2 := h_le
      have h6 : 3 + 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) ≥ -7 / 2 := by
        have h7 : 4*x^2 + 9*y^2 + 4*x + 12*y + 9 ≥ 4 := h_ge
        have h8 : (2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) ) ≤ 1 / 2 := by
          apply (div_le_div_iff (by positivity) (by positivity)).mpr
          nlinarith
        have h9 : (2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9) ) ≥ 0 := by
          apply div_nonneg 
          norm_num
          all_goals linarith
        linarith
      nlinarith
    have h_t_le : ((12*x^2 + 27*y^2 + 12*x + 36*y + 29) / (4*x^2 + 9*y^2 + 4*x + 12*y + 9))^2 ≤ 49/4 := by
      have eq1 : ((12*x^2 + 27*y^2 + 12*x + 36*y + 29) / (4*x^2 + 9*y^2 + 4*x + 12*y + 9))^2 = (3 + 2 / (4*x^2 + 9*y^2 + 4*x + 12*y + 9)) ^ 2 := by 
        rw [h_bound]
      rw [eq1]
      linarith [h_sq]
    linarith [ht, h_t_le]