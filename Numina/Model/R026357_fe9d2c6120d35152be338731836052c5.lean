import Mathlib

theorem algebra_3673 {a b c d : ℝ} (h : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ d ≠ 0) (h1 : a / abs a + b / abs b + c / abs c + d / abs d = 2) :
    a * b * c / abs (a * b * c) + abs (a * b * d) / (a * b * d) + a * c * d / abs (a * c * d) + abs (b * c * d) / (b * c * d) = -2 := by
  rcases h with ⟨ha, hb, hc, hd⟩
  have h2 : a / abs a = 1 ∨ a / abs a = -1 := by
    cases (le_or_lt 0 a) with
    | inl h3 =>
      have h_abs : abs a = a := abs_of_nonneg h3
      rw [h_abs]
      left
      field_simp [ha, hb, hc]
      all_goals linarith
    | inr h3 =>
      have h_abs : abs a = -a := abs_of_neg h3
      rw [h_abs]
      right
      field_simp [ha, hb, hc]
      all_goals linarith
  have h3 : b / abs b = 1 ∨ b / abs b = -1 := by
    cases (le_or_lt 0 b) with
    | inl h4 =>
      have h_abs : abs b = b := abs_of_nonneg h4
      rw [h_abs]
      left
      field_simp [hb, ha, hc]
      all_goals linarith
    | inr h4 =>
      have h_abs : abs b = -b := abs_of_neg h4
      rw [h_abs]
      right
      field_simp [hb, ha, hc]
      all_goals linarith
  have h4 : c / abs c = 1 ∨ c / abs c = -1 := by
    cases (le_or_lt 0 c) with
    | inl h5 =>
      have h_abs : abs c = c := abs_of_nonneg h5
      rw [h_abs]
      left
      field_simp [hc, ha, hb]
      all_goals linarith
    | inr h5 =>
      have h_abs : abs c = -c := abs_of_neg h5
      rw [h_abs]
      right
      field_simp [hc, ha, hb]
      all_goals linarith
  have h5 : d / abs d = 1 ∨ d / abs d = -1 := by
    cases (le_or_lt 0 d) with
    | inl h6 =>
      have h_abs : abs d = d := abs_of_nonneg h6
      rw [h_abs]
      left
      field_simp [hd, ha, hb]
      all_goals linarith
    | inr h6 =>
      have h_abs : abs d = -d := abs_of_neg h6
      rw [h_abs]
      right
      field_simp [hd, ha, hb]
      all_goals linarith
  
  have abs_a_b_c : abs (a * b * c) = abs a * abs b * abs c := by 
    simp [abs_mul]
  
  have abs_a_b_d : abs (a * b * d) = abs a * abs b * abs d := by 
    simp [abs_mul]

  have abs_a_c_d : abs (a * c * d) = abs a * abs c * abs d := by 
    simp [abs_mul]

  have abs_b_c_d : abs (b * c * d) = abs b * abs c * abs d := by 
    simp [abs_mul]

  have h_nonzero_abs : abs a ≠ 0 := abs_ne_zero.mpr ha
  have h_nonzero_abs_b : abs b ≠ 0 := abs_ne_zero.mpr hb
  have h_nonzero_abs_c : abs c ≠ 0 := abs_ne_zero.mpr hc
  have h_nonzero_abs_d : abs d ≠ 0 := abs_ne_zero.mpr hd

  have h21 : a * b * c / abs (a * b * c) = (a / abs a) * (b / abs b) * (c / abs c) := by 
    rw [abs_a_b_c]
    field_simp [ha, hb, hc, h_nonzero_abs, h_nonzero_abs_b, h_nonzero_abs_c]
    <;> ring_nf <;> norm_num [abs_of_pos, abs_of_neg, sq_pos_of_ne_zero ha] 
    <;> ring

  have h22 : abs (a * b * d) / (a * b * d) = (a / abs a) * (b / abs b) * (d / abs d) := by 
    rw [abs_a_b_d]
    field_simp [ha, hb, hd, h_nonzero_abs, h_nonzero_abs_b, h_nonzero_abs_d]
    <;> ring_nf <;> norm_num [abs_of_pos, abs_of_neg, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hd]
    <;> ring

  have h23 : a * c * d / abs (a * c * d) = (a / abs a) * (c / abs c) * (d / abs d) := by 
    rw [abs_a_c_d]
    field_simp [ha, hc, hd, h_nonzero_abs, h_nonzero_abs_c, h_nonzero_abs_d]
    <;> ring_nf <;> norm_num [abs_of_pos, abs_of_neg, sq_pos_of_ne_zero ha, sq_pos_of_ne_zero hd]
    <;> ring

  have h24 : abs (b * c * d) / (b * c * d) = (b / abs b) * (c / abs c) * (d / abs d) := by 
    rw [abs_b_c_d]
    field_simp [hb, hc, hd, h_nonzero_abs_b, h_nonzero_abs_c, h_nonzero_abs_d]
    <;> ring_nf <;> norm_num [abs_of_pos, abs_of_neg, sq_pos_of_ne_zero hb, sq_pos_of_ne_zero hd]
    <;> ring

  rw [h21, h22, h23, h24]

  have hx2 : (a / abs a) ^ 2 = 1 := by 
    have h_a2 : a ^ 2 = a ^ 2 := rfl
    have h_abs_a2 : abs a ^ 2 = a ^ 2 := by 
      rw [sq_abs]
    have h_abs_a2_ne_zero : abs a ^ 2 ≠ 0 := by 
      apply pow_ne_zero 2
      exact abs_ne_zero.mpr ha

    field_simp [ha, h_nonzero_abs]
    <;> nlinarith [abs_nonneg a, sq_pos_of_ne_zero ha, sq_abs a]

  have hy2 : (b / abs b) ^ 2 = 1 := by 
    have h_b2 : b ^ 2 = b ^ 2 := rfl
    have h_abs_b2 : abs b ^ 2 = b ^ 2 := by 
      rw [sq_abs]
    have h_abs_b2_ne_zero : abs b ^ 2 ≠ 0 := by 
      apply pow_ne_zero 2
      exact abs_ne_zero.mpr hb

    field_simp [hb, h_nonzero_abs_b]
    <;> nlinarith [abs_nonneg b, sq_pos_of_ne_zero hb, sq_abs b]

  have hz2 : (c / abs c) ^ 2 = 1 := by 
    have h_c2 : c ^ 2 = c ^ 2 := rfl
    have h_abs_c2 : abs c ^ 2 = c ^ 2 := by 
      rw [sq_abs]
    have h_abs_c2_ne_zero : abs c ^ 2 ≠ 0 := by 
      apply pow_ne_zero 2
      exact abs_ne_zero.mpr hc

    field_simp [hc, h_nonzero_abs_c]
    <;> nlinarith [abs_nonneg c, sq_pos_of_ne_zero hc, sq_abs c]

  have hw2 : (d / abs d) ^ 2 = 1 := by 
    have h_d2 : d ^ 2 = d ^ 2 := rfl
    have h_abs_d2 : abs d ^ 2 = d ^ 2 := by 
      rw [sq_abs]
    have h_abs_d2_ne_zero : abs d ^ 2 ≠ 0 := by 
      apply pow_ne_zero 2
      exact abs_ne_zero.mpr hd

    field_simp [hd, h_nonzero_abs_d]
    <;> nlinarith [abs_nonneg d, sq_pos_of_ne_zero hd, sq_abs d]

  rcases h2 with h2 | h2 <;> rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;> 
    norm_num [h2, h3, h4, h5] at h1 ⊢ <;> nlinarith [hx2, hy2, hz2, hw2, sq_nonneg (a / abs a - 1), sq_nonneg (b / abs b - 1), sq_nonneg (c / abs c - 1), sq_nonneg (d / abs d - 1)]