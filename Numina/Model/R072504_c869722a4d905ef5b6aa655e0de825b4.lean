import Mathlib

theorem algebra_177170 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hsum : a + b + c ≠ 0) (h : 1 / a + 1 / b + 1 / c = 1 / (a + b + c)) :
    1 / a ^ 1999 + 1 / b ^ 1999 + 1 / c ^ 1999 = 1 / (a ^ 1999 + b ^ 1999 + c ^ 1999) := by

  field_simp [ha, hb, hc, hsum] at h 
  have h2 : (a + b) * (b + c) * (c + a) = 0 := by 
    nlinarith [sq_pos_of_ne_zero (show a + b + c ≠ 0 by exact hsum), sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hc]
  
  cases' (mul_eq_zero.mp h2) with h3 h4
  cases' (mul_eq_zero.mp h3) with h5 h6
  · -- Case where $a + b = 0$ implies $c + a \neq 0$ and $b + c \neq 0$.
    have hab : a + b = 0 := h5
    have h7 : a = -b := by linarith 
    have ha1999 : a ^ 1999 = (-1) * b ^ 1999 := by 
      rw [h7]
      ring_nf 
    have ha1999_eq : 1 / a ^ 1999 = - 1 / b ^ 1999 := by 
      rw [ha1999]
      field_simp [hb]
    have hsum1999 : 1 / a ^ 1999 + 1 / b ^ 1999 + 1 / c ^ 1999 = 1 / c ^ 1999 := by 
      rw [ha1999_eq]
      ring 
    have hden1999 : a ^ 1999 + b ^ 1999 + c ^ 1999 = c ^ 1999 := by 
      rw [ha1999]
      ring 
    rw [hsum1999, hden1999]
    all_goals field_simp [hc]
  
  · -- Case where $b + c = 0$ implies $a + b \neq 0$ and $c + a \neq 0$.
    have hbc : b + c = 0 := h6
    have hb1 : b = -c := by linarith 
    have hb1999 : b ^ 1999 = (-1) * c ^ 1999 := by 
      rw [hb1]
      ring_nf 
    have hb1999_eq : 1 / b ^ 1999 = - 1 / c ^ 1999 := by 
      rw [hb1999]
      field_simp [hc]
    have hsum1999 : 1 / a ^ 1999 + 1 / b ^ 1999 + 1 / c ^ 1999 = 1 / a ^ 1999 := by 
      rw [hb1999_eq]
      ring 
    have hden1999 : a ^ 1999 + b ^ 1999 + c ^ 1999 = a ^ 1999 := by 
      rw [hb1999]
      ring 
    rw [hsum1999, hden1999]
    all_goals field_simp [ha]

  · -- Case where $c + a = 0$ implies $a + b \neq 0$ and $b + c \neq 0$.
    have hca : c + a = 0 := h4
    have hc1 : c = -a := by linarith 
    have hc1999 : c ^ 1999 = (-1) * a ^ 1999 := by 
      rw [hc1]
      ring_nf 
    have hca1999_eq : 1 / c ^ 1999 = - 1 / a ^ 1999 := by 
      rw [hc1999]
      field_simp [ha]
    have hsum1999 : 1 / a ^ 1999 + 1 / b ^ 1999 + 1 / c ^ 1999 = 1 / b ^ 1999 := by 
      rw [hca1999_eq]
      ring 
    have hden1999 : a ^ 1999 + b ^ 1999 + c ^ 1999 = b ^ 1999 := by 
      rw [hc1999]
      ring 
    rw [hsum1999, hden1999]
    all_goals field_simp [hb]