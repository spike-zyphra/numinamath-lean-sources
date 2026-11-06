import Mathlib

theorem algebra_205802 {x y : ℝ} (h : y ≠ 0) (h' : x ≠ 0) (h'' : (x + 22) / y + (290 / (x * y)) = (26 - y) / x) :
    x * y = -143 := by
  have eq1 : x * (x + 22) + 290 = y * (26 - y) := by
    have h1 : x * y ≠ 0 := by 
      apply mul_ne_zero
      exact h'
      exact h
    have eq2 : (x + 22) / y + (290 / (x * y)) = (26 - y) / x := h''
    have eq3 : ((x + 22) / y + (290 / (x * y))) * (x * y) = ((26 - y) / x) * (x * y) := by
      rw [eq2]
    have eq4 : ((x + 22) / y + (290 / (x * y))) * (x * y) = x * (x + 22) + 290 := by
      have eq5 : ((x + 22) / y + (290 / (x * y))) * (x * y) =
        ((x + 22) / y) * (x * y) + (290 / (x * y)) * (x * y) := by ring
      rw [eq5]
      have eq6 : ((x + 22) / y) * (x * y) = x * (x + 22) := by
        field_simp [h]
        <;> ring
      have eq7 : (290 / (x * y)) * (x * y) = 290 := by 
        field_simp [h', h]
      rw [eq6, eq7]
    have eq8 : ((26 - y) / x) * (x * y) = y * (26 - y) := by 
      field_simp [h']
      <;> ring
    rw [eq4, eq8] at eq3
    linarith
  have eq2 : (x + 11) ^ 2 + (y - 13) ^ 2 = 0 := by 
    nlinarith [eq1]
  have h11 : (x + 11) ^ 2 = 0 := by 
    linarith [sq_nonneg (x + 11), sq_nonneg (y - 13)]
  have h12 : x + 11 = 0 := by
    rw [sq_eq_zero_iff] at h11
    linarith
  have h13 : (y - 13) ^ 2 = 0 := by 
    linarith [sq_nonneg (x + 11), sq_nonneg (y - 13)]
  have h14 : y - 13 = 0 := by 
    rw [sq_eq_zero_iff] at h13
    linarith
  have hx : x = -11 := by linarith
  have hy : y = 13 := by linarith
  rw [hx, hy]
  all_goals norm_num