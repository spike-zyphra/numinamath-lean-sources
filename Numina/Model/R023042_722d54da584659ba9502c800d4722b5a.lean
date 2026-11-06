import Mathlib

theorem algebra_100948 {a b c : ℚ} (h₀ : a * b / (a + b) = 2^2012 / 3)
    (h₁ : b * c / (b + c) = 2^2013 / 3) (h₂ : a * c / (a + c) = 2^2013 / 5) :
    ∃ n : ℕ, Real.sqrt (3 * (b - a) * (c - b) * (c - a)) = n := by
  have h3 : a + b ≠ 0 := by
    by_contra h
    have h4 : a * b / (a + b) = 0 := by
      rw [h]
      norm_num
    linarith
  have h4 : b + c ≠ 0 := by
    by_contra h
    have h5 : b * c / (b + c) = 0 := by
      rw [h]
      norm_num
    linarith
  have h5 : a + c ≠ 0 := by
    by_contra h
    have h6 : a * c / (a + c) = 0 := by
      rw [h]
      norm_num
    linarith
  have eq1 : a * b = (2^2012 / 3) * (a + b) := by
    have hne : a + b ≠ 0 := h3
    field_simp at h₀ ⊢
    linarith
  have eq2 : b * c = (2^2013 / 3) * (b + c) := by
    have hne : b + c ≠ 0 := h4
    field_simp at h₁ ⊢
    linarith
  have eq3 : a * c = (2^2013 / 5) * (a + c) := by
    have hne : a + c ≠ 0 := h5
    field_simp at h₂ ⊢
    linarith
  have eq4 : 1 / a + 1 / b = 3 / (2^2012 : ℚ) := by
    have hne1 : a ≠ 0 := by
      by_contra h
      rw [h] at eq1 h₀ 
      field_simp at eq1 h₀
      all_goals linarith
    have hne2 : b ≠ 0 := by
      by_contra h
      rw [h] at eq1 h₀ 
      field_simp at eq1 h₀
      all_goals linarith
    field_simp at eq1 ⊢
    nlinarith [sq_pos_of_ne_zero hne1, sq_pos_of_ne_zero hne2]
  have eq5 : 1 / b + 1 / c = 3 / (2^2013 : ℚ) := by
    have hne1 : b ≠ 0 := by
      by_contra h
      rw [h] at eq2 h₁ 
      field_simp at eq2 h₁
      all_goals linarith
    have hne2 : c ≠ 0 := by
      by_contra h
      rw [h] at eq2 h₁ 
      field_simp at eq2 h₁
      all_goals linarith
    field_simp at eq2 ⊢
    nlinarith [sq_pos_of_ne_zero hne1, sq_pos_of_ne_zero hne2]
  have eq6 : 1 / a + 1 / c = 5 / (2^2013 : ℚ) := by
    have hne1 : a ≠ 0 := by
      by_contra h
      rw [h] at eq3 h₂ 
      field_simp at eq3 h₂
      all_goals linarith
    have hne2 : c ≠ 0 := by
      by_contra h
      rw [h] at eq3 h₂ 
      field_simp at eq3 h₂
      all_goals linarith
    field_simp at eq3 ⊢
    nlinarith [sq_pos_of_ne_zero hne1, sq_pos_of_ne_zero hne2]
  have eq7 : 1 / a = 4 / (2^2013 : ℚ) := by
    linarith [eq4, eq5, eq6]
  have eq8 : 1 / b = 2 / (2^2013 : ℚ) := by
    linarith [eq4, eq5, eq6]
  have eq9 : 1 / c = 1 / (2^2013 : ℚ) := by
    linarith [eq4, eq5, eq6]
  have ha : a = 2^2011 := by
    have hne1 : a ≠ 0 := by
      by_contra h
      rw [h] at eq7
      field_simp at eq7
    have h10 : 1 / a = 4 / (2^2013 : ℚ) := eq7
    have h11 : a = 2^2011 := by
      field_simp at h10 ⊢
      nlinarith [sq_pos_of_ne_zero hne1]
    exact h11
  have hb : b = 2^2012 := by
    have hne1 : b ≠ 0 := by
      by_contra h
      rw [h] at eq8
      field_simp at eq8
    have h10 : 1 / b = 2 / (2^2013 : ℚ) := eq8
    have h11 : b = 2^2012 := by
      field_simp at h10 ⊢
      nlinarith [sq_pos_of_ne_zero hne1]
    exact h11
  have hc : c = 2^2013 := by
    have hne1 : c ≠ 0 := by
      by_contra h
      rw [h] at eq9
      field_simp at eq9
    have h10 : 1 / c = 1 / (2^2013 : ℚ) := eq9
    have h11 : c = 2^2013 := by
      field_simp at h10 ⊢
      nlinarith [sq_pos_of_ne_zero hne1]
    exact h11
  have h15 : (3 * ((b : ℝ) - (a : ℝ)) * ((c : ℝ) - (b : ℝ)) * ((c : ℝ) - (a : ℝ))) = (9 * (2^6034 : ℝ)) := by
    rw [show (b : ℝ) = (2^2012 : ℝ) by exact_mod_cast hb, 
        show (a : ℝ) = (2^2011 : ℝ) by exact_mod_cast ha, 
        show (c : ℝ) = (2^2013 : ℝ) by exact_mod_cast hc]
    norm_num
  have h16 : Real.sqrt (9 * (2^6034 : ℝ)) = (3 * 2^3017 : ℝ) := by
    rw [Real.sqrt_eq_iff_sq_eq] <;> norm_num
  use 3 * 2^3017
  rw [h15, h16]
  all_goals norm_num