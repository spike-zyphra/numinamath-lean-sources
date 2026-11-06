import Mathlib
open Real
theorem algebra_324107 {a b c : ℝ} (h1 : a * b / (a + b) = 1 / 3) (h2 : b * c / (b + c) = 1 / 4)
(h3 : a * c / (c + a) = 1 / 5) : a * b * c / (a * b + b * c + c * a) = 1 / 6:= by

  -- Ensure denominators are not zero
  have ha1 : a + b ≠ 0 := by 
    by_contra h 
    have eq : a * b / (a + b) = 0 := by 
      rw [h] 
      norm_num 
    linarith 
  have hb1 : b + c ≠ 0 := by 
    by_contra h 
    have eq : b * c / (b + c) = 0 := by 
      rw [h]
      norm_num 
    linarith 
  have hc1 : c + a ≠ 0 := by 
    by_contra h 
    have eq : a * c / (c + a) = 0 := by 
      rw [h]
      norm_num 
    linarith 
  -- Derive that a, b, c are all non-zero
  have ha2 : a ≠ 0 := by 
    by_contra h 
    have ha : a = 0 := by linarith 
    rw [ha] at h1 
    simp at h1 
  -- Derive that a, b, c are all non-zero
  have hb2 : b ≠ 0 := by 
    by_contra h 
    have hb : b = 0 := by linarith 
    rw [hb] at h1 
    simp at h1 
  -- Derive that a, b, c are all non-zero
  have hc2 : c ≠ 0 := by 
    by_contra h 
    have hc : c = 0 := by linarith 
    rw [hc] at h3 
    simp at h3 
  -- From h1: Convert to 1/a + 1/b = 3 
  have eq1 : 1 / a + 1 / b = 3 := by 
    have h1' : a * b / (a + b) = 1 / 3 := h1 
    have h4 : a + b ≠ 0 := by 
      exact ha1 
    have h5 : a ≠ 0 := ha2 
    have h6 : b ≠ 0 := hb2 
    field_simp [h5, h6, h4] at h1' ⊢ 
    <;> linarith 
  -- From h2: Convert to 1/b + 1/c = 4 
  have eq2 : 1 / b + 1 / c = 4 := by 
    have h2' : b * c / (b + c) = 1 / 4 := h2 
    have h7 : b + c ≠ 0 := by 
      exact hb1 
    have h8 : b ≠ 0 := hb2 
    have h9 : c ≠ 0 := hc2 
    field_simp [h8, h9, h7] at h2' ⊢ 
    <;> linarith 
  -- From h3: Convert to 1/a + 1/c = 5 
  have eq3 : 1 / a + 1 / c = 5 := by 
    have h3' : a * c / (c + a) = 1 / 5 := h3 
    have h10 : c + a ≠ 0 := by 
      exact hc1 
    have h11 : c ≠ 0 := hc2 
    have h12 : a ≠ 0 := ha2 
    field_simp [h11, h12, h10] at h3' ⊢ 
    <;> linarith 
  -- Add equations to get 1/a + 1/b + 1/c = 6 
  have eq4 : 1 / a + 1 / b + 1 / c = 6 := by 
    linarith [eq1, eq2, eq3]
  -- Now converting this to the required form.
  have eq5 : a * b + b * c + c * a = (a * b * c) * ( (1 / a) + (1 / b) + (1 / c) ) := by 
    have ha3 : a ≠ 0 := ha2 
    have hb3 : b ≠ 0 := hb2 
    have hc3 : c ≠ 0 := hc2 
    field_simp [ha3, hb3, hc3] 
    ring 
  -- Simplify to (a * b * c) * 6
  have eq6 : a * b + b * c + c * a = (a * b * c) * 6 := by 
    rw [eq5]
    rw [eq4] 
    all_goals norm_num 
  have eq7 : (a * b * c / (a * b + b * c + c * a)) = 1 / 6 := by 
    rw [eq6]
    have ha3 : a ≠ 0 := ha2 
    have hb3 : b ≠ 0 := hb2 
    have hc3 : c ≠ 0 := hc2 
    have ha4 : a * b * c ≠ 0 := by 
      apply mul_ne_zero 
      apply mul_ne_zero 
      exact ha3 
      exact hb3 
      exact hc3 
    field_simp [ha4] 
    all_goals 
      nlinarith 
  exact eq7