import Mathlib

theorem algebra_137045 {a b c : ℝ} (ha : a ≠ -b) (hb : b ≠ -c) (hc : c ≠ -a)
    (h1 : a * b / (a + b) = 3) (h2 : b * c / (b + c) = 5) (h3 : c * a / (c + a) = 8) :
    a * b * c / (a * b + b * c + c * a) = 240 / 79 := by
  have h4 : a + b ≠ 0 := by
    intro h
    apply ha
    linarith 
  have h5 : b + c ≠ 0 := by
    intro h
    apply hb
    linarith 
  have h6 : c + a ≠ 0 := by
    intro h
    apply hc
    linarith 
  -- From h1: a * b = 3 * (a + b)
  have h7 : a * b = 3 * (a + b) := by 
    have h4' : a + b ≠ 0 := h4
    field_simp [h4'] at h1 ⊢
    linarith 
  -- From h2: b * c = 5 * (b + c)
  have h8 : b * c = 5 * (b + c) := by 
    have h5' : b + c ≠ 0 := h5 
    field_simp [h5'] at h2 ⊢
    linarith 
  -- From h3: c * a = 8 * (c + a)
  have h9 : c * a = 8 * (c + a) := by 
    have h6' : c + a ≠ 0 := h6 
    field_simp [h6'] at h3 ⊢
    linarith 
  -- Proof a ≠ 0
  have ha1 : a ≠ 0 := by
    intro ha_eq_0 -- Assume a = 0 
    -- From h7: a * b = 3 * (a + b). Substitute a=0.
    have h7' : (0 : ℝ) * b = 3 * (0 + b) := by 
      rw [ha_eq_0] at h7
      linarith [h7]
    -- This simplifies to 0 = 3 * b, which implies b = 0.
    have hb_eq_0 : b = 0 := by 
      nlinarith [h7'] 
    -- But then a + b = 0 + 0 = 0, contradicting h4 : a + b ≠ 0.
    have h4_contr : (a + b) = (0 : ℝ) := by 
      nlinarith [ha_eq_0, hb_eq_0, h7'] 
    -- We have h4 : a + b ≠ 0 and h4_contr : a + b = 0. This is a contradiction.
    exfalso
    tauto 
  -- Proof b ≠ 0
  have hb1 : b ≠ 0 := by
    intro hb_eq_0 -- Assume b = 0 
    -- From h8: b * c = 5 * (b + c). Substitute b=0.
    have h8' : (0 : ℝ) * c = 5 * (0 + c) := by 
      rw [hb_eq_0] at h8
      linarith [h8]
    -- This simplifies to 0 = 5 * c, which implies c = 0.
    have hc_eq_0 : c = 0 := by 
      nlinarith [h8'] 
    -- But then b + c = 0 + 0 = 0, contradicting h5 : b + c ≠ 0.
    have h5_contr : (b + c) = (0 : ℝ) := by 
      nlinarith [hb_eq_0, hc_eq_0, h8'] 
    -- We have h5 : b + c ≠ 0 and h5_contr : b + c = 0. This is a contradiction.
    exfalso
    tauto 
  -- Proof c ≠ 0
  have hc1 : c ≠ 0 := by
    intro hc_eq_0 -- Assume c = 0 
    -- From h9: c * a = 8 * (c + a). Substitute c=0.
    have h9' : (0 : ℝ) * a = 8 * (0 + a) := by 
      rw [hc_eq_0] at h9
      linarith [h9]
    -- This simplifies to 0 = 8 * a, which implies a = 0.
    have ha_eq_0 : a = 0 := by 
      nlinarith [h9'] 
    -- But then c + a = 0 + 0 = 0, contradicting h6 : c + a ≠ 0.
    have h6_contr : (c + a) = (0 : ℝ) := by 
      nlinarith [hc_eq_0, ha_eq_0, h9'] 
    -- We have h6 : c + a ≠ 0 and h6_contr : c + a = 0. This is a contradiction.
    exfalso
    tauto 
  -- Equation to compute the final expression
  have h14 : a * b * c / (a * b + b * c + c * a) = 1 / (1/a + 1/b + 1/c) := by 
    field_simp [ha1, hb1, hc1]
    <;> ring_nf <;> field_simp [ha1, hb1, hc1]
    <;> ring_nf <;> nlinarith 
  -- Solving Futher expression
  have h10 : 1 / a + 1 / b = 1 / 3 := by 
    field_simp [ha1, hb1]
    nlinarith 
  -- Solving Futher expression
  have h11 : 1 / b + 1 / c = 1 / 5 := by 
    field_simp [hb1, hc1]
    nlinarith 
  -- Solving Futher expression
  have h12 : 1 / c + 1 / a = 1 / 8 := by 
    field_simp [hc1, ha1]
    nlinarith 
  -- Solving Final expression
  have h15 : 1 / a + 1 / b + 1 / c = 79 / 240 := by 
    linarith [h10, h11, h12] 
  rw [h14, h15]
  all_goals norm_num 
  all_goals norm_num 
  all_goals norm_num 
  <;> linarith 
  all_goals norm_num 
  all_goals norm_num