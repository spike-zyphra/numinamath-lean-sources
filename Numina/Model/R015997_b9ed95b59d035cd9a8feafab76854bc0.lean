import Mathlib

theorem algebra_929 (a b c : ℝ) (h₀ : a ≠ -b) (h₁ : b ≠ -c) (h₂ : c ≠ -a)
    (h₃ : (a * b) / (a + b) = 1 / 3) (h₄ : (b * c) / (b + c) = 1 / 4) (h₅ : (c * a) / (c + a) = 1 / 5) :
    (a * b * c) / (a * b + b * c + c * a) = 1 / 6 := by

  have h6 : a + b ≠ 0 := by
    intro h
    apply h₀
    linarith

  -- Transform h₃ to 3 * (a * b) = a + b
  have eq1 : 3 * (a * b) = a + b := by
    have h6' : a + b ≠ 0 := h6
    have eq1 : (a * b) / (a + b) = 1 / 3 := h₃
    field_simp [h6'] at eq1 ⊢
    linarith

  have h7 : b + c ≠ 0 := by
    intro h
    apply h₁
    linarith

  -- Transform h₄ to 4 * (b * c) = b + c
  have eq2 : 4 * (b * c) = b + c := by
    have h7' : b + c ≠ 0 := h7
    have eq2 : (b * c) / (b + c) = 1 / 4 := h₄
    field_simp [h7'] at eq2 ⊢
    linarith

  have h8 : c + a ≠ 0 := by
    intro h
    apply h₂
    linarith

  -- Transform h₅ to 5 * (c * a) = c + a
  have eq3 : 5 * (c * a) = c + a := by
    have h8' : c + a ≠ 0 := h8
    have eq3 : (c * a) / (c + a) = 1 / 5 := h₅
    field_simp [h8'] at eq3 ⊢
    linarith

  have ha1 : a ≠ 0 := by
    by_contra h
    have h9 : a = 0 := by linarith
    rw [h9] at eq1
    have h11 : b = 0 := by nlinarith
    have h12 : a + b = 0 := by
      linarith [h9, h11]
    tauto

  have hb1 : b ≠ 0 := by 
    by_contra h
    have h9 : b = 0 := by linarith 
    rw [h9] at eq1
    have h13 : a = 0 := by 
      nlinarith
    have h12 : a + b = 0 := by
      linarith [h13, h9]
    tauto

  have hc1 : c ≠ 0 := by
    by_contra h
    have h9 : c = 0 := by linarith 
    rw [h9] at eq3
    have h14 : a = 0 := by 
      nlinarith 
    have h12 : c + a = 0 := by
      linarith [h9, h14]
    tauto

  -- Derive reciprocals
  have eq4 : 1 / a + 1 / b = 3 := by
    have h9 : a ≠ 0 := ha1
    have h10 : b ≠ 0 := hb1
    field_simp [h9, h10] at eq1 ⊢
    nlinarith 
  -- Derive reciprocals
  have eq5 : 1 / b + 1 / c = 4 := by
    have h9 : b ≠ 0 := hb1
    have h10 : c ≠ 0 := hc1
    field_simp [h9, h10] at eq2 ⊢
    nlinarith 
  -- Derive reciprocals
  have eq6 : 1 / c + 1 / a = 5 := by
    have h9 : c ≠ 0 := hc1
    have h10 : a ≠ 0 := ha1
    field_simp [h9, h10] at eq3 ⊢
    nlinarith 

  have eq7 : 1 / b = 1 := by
    linarith [eq4, eq5, eq6]

  have hb2 : b = 1 := by
    have h1 : 1 / b = 1 := eq7
    have h2 : b ≠ 0 := hb1
    field_simp [h2] at h1 ⊢
    all_goals linarith [h1]

  -- Derive reciprocal of a
  have eq8 : 1 / a = 2 := by
    rw [hb2] at eq4
    linarith

  -- Derive a
  have ha2 : a = 1 / 2 := by
    have h1 : 1 / a = 2 := eq8
    have h2 : a ≠ 0 := ha1
    field_simp [h2] at h1 ⊢
    all_goals linarith [h1]

  have eq9 : 1 / c = 3 := by
    rw [hb2] at eq5
    linarith

  -- Derive c
  have hc2 : c = 1 / 3 := by
    have h1 : 1 / c = 3 := eq9
    have h2 : c ≠ 0 := hc1
    field_simp [h2] at h1 ⊢
    all_goals linarith [h1]

  -- Compute $abc$:
  have habc : a * b * c = 1 / 6 := by 
    rw [ha2, hb2, hc2]
    norm_num 
  -- Compute $ab + bc + ca$:
  have hab : a * b = 1 / 2 := by
    rw [ha2, hb2]
    norm_num 
  have hbc : b * c = 1 / 3 := by 
    rw [hb2, hc2]
    norm_num 
  have hca : c * a = 1 / 6 := by
    rw [hc2, ha2]
    norm_num 
  have habbc : a * b + b * c + c * a = 1 := by
    linarith [hab, hbc, hca] 
  -- Compute the final expression:
  rw [habc, habbc]
  all_goals norm_num