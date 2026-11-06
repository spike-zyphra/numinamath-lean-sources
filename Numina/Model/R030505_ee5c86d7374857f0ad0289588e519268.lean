import Mathlib

theorem algebra_322758 (a b c : ℝ) (ha : a ≠ 0) (h : ∃! x : ℝ, x > 0 ∧ a * x ^ 2 + b * x + c = 0 ∧ c * x ^ 2 + b * x + a = 0) :
    a + b + c = 0 := by
  rcases h with ⟨x, ⟨hx_pos, heq1, heq2⟩, h1⟩
  have eq1 : a * x ^ 2 + b * x + c = 0 := heq1 
  have eq2 : c * x ^ 2 + b * x + a = 0 := heq2 
  have eq3 : (a - c) * (x ^ 2 - 1) = 0 := by 
    nlinarith 
  cases' (mul_eq_zero.mp eq3) with h2 h3 
  · -- h2 means a - c = 0, so a = c 
    have h4 : a = c := by linarith 
    have eq1_a : a * x ^ 2 + b * x + a = 0 := by 
      have eq1' : a * x ^ 2 + b * x + c = 0 := heq1 
      rw [show c = a by linarith [h4]] at eq1'
      linarith 
    have eq3_a : a * (1/x) ^ 2 + b * (1/x) + a = 0 := by 
      have eq4 : a * x ^ 2 + b * x + a = 0 := eq1_a 
      have hx1_pos : x ≠ 0 := by linarith 
      field_simp at *
      nlinarith [eq4, mul_pos hx_pos hx_pos] 
    have eq6 : 1/x > 0 := by 
      apply div_pos 
      norm_num 
      all_goals linarith 
    have eq7 : 1/x = x := by 
      have h_eq1 : (1/x : ℝ) > 0 := eq6 
      have h_eq2 : a * (1/x) ^ 2 + b * (1/x) + c = 0 := by 
        rw [show c = a by linarith [h4]] 
        linarith [eq3_a] 
      have h_eq3 : c * (1/x) ^ 2 + b * (1/x) + a = 0 := by 
        rw [show c = a by linarith [h4]] 
        nlinarith [eq3_a] 
      have h8 := h1 (1/x) ⟨eq6, h_eq2, h_eq3⟩ 
      linarith 
    have hx3 : x = 1 := by
      have hx4 : x * x = 1 := by 
        have eq7' : (1 / x) = x := by linarith [eq7]
        field_simp at eq7' ⊢
        all_goals nlinarith
      have hx4' : x ^ 2 = 1 := by 
        nlinarith 
      have hx5 : x = 1 ∨ x = -1 := by 
        rw [sq_eq_one_iff] at hx4'
        tauto 
      cases hx5 with
      | inl h => exact h 
      | inr h => 
        nlinarith [h, hx_pos] 
    have : a + b + c = 0 := by 
      have eq1_a' : a * x ^ 2 + b * x + a = 0 := eq1_a 
      rw [hx3] at eq1_a' 
      have eq9 : a + b + a = 0 := by 
        linarith 
      have eq10 : a + b + c = 0 := by 
        have eq11 : c = a := by linarith [h4] 
        rw [eq11] 
        linarith [eq9] 
      assumption 
    assumption 
  · -- h3 means x ^2 -1 = 0, so x = 1 
    have eq8 : x ^2 = 1 := by 
      linarith 
    have hx1 : x = 1 := by 
      have hx2' : x ^ 2 - 1 = 0 := by linarith 
      have hx2'' : (x - 1) * (x + 1) = 0 := by 
        nlinarith 
      cases' (mul_eq_zero.mp hx2'') with h6 h7 
      · -- h6 means x - 1 = 0, so x = 1 
        linarith 
      · -- h7 means x + 1 = 0, so x = -1 
        nlinarith 
    rw [hx1] at eq1 
    have : a + b + c = 0 := by 
      linarith 
    assumption