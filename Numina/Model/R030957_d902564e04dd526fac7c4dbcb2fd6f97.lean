import Mathlib

theorem algebra_1156
    (a b c : ℤ)
    (ha : 0 < a)
    (hb : 0 < b)
    (hc : 0 < c)
    (h1 : (a / b : ℚ) = c / 9)
    (h2 : (a + c : ℝ) ^ 2 / (b + 9) ^ 2 = 4 / 9)
    (h3 : a ^ 2 + b ^ 2 + c ^ 2 = 49) :
    b = 3 ∧ c = 6 := by
  have h1' : (a : ℚ) * 9 = (b : ℚ) * (c : ℚ) := by 
    have h1 : (a / b : ℚ) = c / 9 := by assumption
    have h4 : (b : ℚ) ≠ 0 := by 
      exact_mod_cast (show b ≠ 0 by nlinarith)
    field_simp [h4] at h1 ⊢
    linarith
  have h1'1 : (a : ℤ) * 9 = b * c := by
    exact_mod_cast h1'
  have h21 : (a + c : ℝ) / (b + 9 : ℝ) = 2 / 3 := by 
    have h2 : (a + c : ℝ) ^ 2 / (b + 9) ^ 2 = 4 / 9 := by assumption
    have h5 : (b + 9 : ℝ) ≠ 0 := by
      have hb_pos : (b : ℝ) > (0 : ℝ) := by exact_mod_cast hb
      nlinarith
    have h6 : ((a + c : ℝ) / (b + 9 : ℝ)) ^ 2 = 4 / 9 := by 
      field_simp at h2 ⊢
      nlinarith
    have h7 : (a + c : ℝ) / (b + 9 : ℝ) = 2 / 3 ∨ ( (a + c : ℝ) / (b + 9 : ℝ) ) = -2 / 3 := by
      have h8 : ((a + c : ℝ) / (b + 9 : ℝ)) ^ 2 - 4 / 9 = 0 := by nlinarith
      have h9 : ((a + c : ℝ) / (b + 9 : ℝ) - 2 / 3) * (( (a + c : ℝ) / (b + 9 : ℝ) ) + 2 / 3) = 0 := by
        ring_nf at h8 ⊢
        nlinarith
      cases (mul_eq_zero.1 h9) with
      | inl h10 =>
        left
        linarith 
      | inr h11 =>
        right
        linarith
    cases h7 with
    | inl h11 =>
      linarith
    | inr h11 =>
      have h13 : (a + c : ℝ) > 0 := by
        nlinarith [show (a : ℝ) > 0 by exact_mod_cast ha, show (c : ℝ) > 0 by exact_mod_cast hc]
      have h14 : (b + 9 : ℝ) > 0 := by 
        nlinarith [show (b : ℝ) > 0 by exact_mod_cast hb]
      have h15 : (a + c : ℝ) / (b + 9 : ℝ) > 0 := by 
        apply div_pos 
        linarith
        linarith
      linarith
  have h21' : (a + c : ℤ) * 3 = 2 * (b + 9 : ℤ) := by
    have h22 : (a + c : ℝ) * 3 = 2 * (b + 9 : ℝ) := by
      field_simp at h21 ⊢ 
      nlinarith 
    rw [show (a + c : ℝ) = (a + c : ℤ) by simp, show (b + 9 : ℝ) = (b + 9 : ℤ) by simp] at h22 
    exact_mod_cast h22 
  have h4 : (b + 9) * (c - 6) = 0 := by 
    nlinarith [sq_nonneg (a : ℤ), sq_nonneg (b : ℤ), sq_nonneg (c : ℤ), h1'1, h21', h3] 
  cases (mul_eq_zero.1 h4) with
  | inl h6 =>
    nlinarith
  | inr h7 =>
    have hc6 : c = 6 := by linarith 
    have hb3 : b = 3 := by 
      have h41 : (b : ℤ) ^ 2 = 9 := by 
        nlinarith [sq_nonneg (a : ℤ), h1'1, h3, hc6]
      have h42 : (b : ℤ) = 3 ∨ (b : ℤ) = -3 := by 
        have h43 : (b : ℤ) ^ 2 = 9 := by assumption 
        have : (b : ℤ) = 3 ∨ (b : ℤ) = -3 := by 
          have h44 : (b : ℤ) ^ 2 = 9 := by assumption 
          have h45 : (b : ℤ) ≤ 3 := by nlinarith [sq_nonneg ((b : ℤ) - 3)]
          have h46 : (b : ℤ) ≥ -3 := by nlinarith [sq_nonneg ((b : ℤ) + 3)]
          interval_cases (b : ℤ) <;> try { tauto }
          all_goals nlinarith 
        assumption 
      cases h42 with 
      | inl h5 => 
        exact_mod_cast h5 
      | inr h5 => 
        nlinarith 
    constructor 
    · -- Show that b = 3 
      exact hb3 
    · -- Show that c = 6 
      exact hc6