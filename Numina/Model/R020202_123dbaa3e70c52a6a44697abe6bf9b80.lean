import Mathlib

theorem algebra_242813 {a b c : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (h1 : (a + b) / (a * b) = 1) (h2 : (b + c) / (b * c) = 1 / 2) (h3 : (c + a) / (c * a) = 1 / 4) :
    a = 8 / 3 ∧ b = 8 / 5 ∧ c = -8 := by

  have eq1 : 1 / a + 1 / b = 1 := by
    have h11 : a * b ≠ 0 := mul_ne_zero ha hb
    field_simp at h1 ⊢
    linarith

  have eq2 : 1 / b + 1 / c = 1 / 2 := by 
    have h22 : b * c ≠ 0 := mul_ne_zero hb hc
    field_simp at h2 ⊢
    linarith

  have eq3 : 1 / c + 1 / a = 1 / 4 := by 
    have h33 : c * a ≠ 0 := mul_ne_zero hc ha
    field_simp at h3 ⊢
    linarith

  have eq4 : (1 / a) = 3 / 8 := by 
    linarith [eq1, eq2, eq3]

  have eq5 : (1 / b) = 5 / 8 := by 
    linarith [eq1, eq2, eq3]

  have eq6 : (1 / c) = -1 / 8 := by 
    linarith [eq1, eq2, eq3]

  have ha2 : a = 8 / 3 := by 
    have hne : a ≠ 0 := ha
    field_simp at eq4 ⊢
    linarith

  have hb2 : b = 8 / 5 := by 
    have hne : b ≠ 0 := hb
    field_simp at eq5 ⊢
    linarith

  have hc2 : c = -8 := by 
    have hne : c ≠ 0 := hc
    field_simp at eq6 ⊢
    linarith

  exact ⟨ha2, hb2, hc2⟩