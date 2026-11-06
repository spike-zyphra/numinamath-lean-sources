import Mathlib

theorem number_theory_240624 (x y : ℚ) (hx : x > 0) (hy : y > 0)
    (h : x + y = 93 / 91) (h1 : x.den = 7) (h2 : y.den = 13) :
    x = 5 / 7 ∧ y = 4 / 13 := by
  have eq1 : x = x.num / x.den := by
    rw [Rat.num_div_den x]
  have eq2 : y = y.num / y.den := by
    rw [Rat.num_div_den y]
  rw [h1] at eq1
  rw [h2] at eq2
  rw [eq1, eq2] at h 
  have eq3 : (x.num : ℚ) * 13 + (y.num : ℚ) * 7 = 93 := by 
    field_simp at h ⊢
    nlinarith 
  have eq4 : (x.num : ℤ) * 13 + (y.num : ℤ) * 7 = 93 := by 
    exact_mod_cast eq3

  have hx5 : x.num > 0 := by 
    have hx_pos : x > 0 := hx 
    rw [eq1] at hx_pos 
    have : (x.num : ℚ) / (7 : ℚ) > 0 := by linarith 
    have hx2 : (x.num : ℚ) > 0 := by 
      apply div_pos_iff.mp at this 
      cases this with 
      | inl h1 => linarith 
      | inr h2 => 
        linarith 
    exact_mod_cast hx2 

  have hy6 : y.num > 0 := by 
    have hy_pos : y > 0 := hy
    rw [eq2] at hy_pos
    have : (y.num : ℚ) / (13 : ℚ) > 0 := by linarith 
    have hy2 : (y.num : ℚ) > 0 := by 
      apply div_pos_iff.mp at this 
      cases this with 
      | inl h1 => linarith 
      | inr h2 => 
        linarith 
    exact_mod_cast hy2 

  have hx5h : x = 5 / 7 := by 
    have h7 : x.num = 5 := by 
      omega 
    rw [eq1] 
    rw [h7] 
    all_goals norm_num

  have hy8h : y = 4 / 13 := by 
    have h7 : y.num = 4 := by 
      omega 
    rw [eq2] 
    rw [h7] 
    all_goals norm_num 
  exact ⟨hx5h, hy8h⟩