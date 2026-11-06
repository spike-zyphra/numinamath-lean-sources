import Mathlib

theorem algebra_4610 {a b c : ℚ} (h₀ : a / b = 2 / 3) (h₁ : b / c = 3 / 5)
    (h₂ : a^2 + b^2 + c^2 = a * b * c) :
    a + b + c = 38 / 3 := by 
  have hb : b ≠ 0 := by 
    by_contra h
    rw [h] at h₀
    norm_num at h₀
  have hc : c ≠ 0 := by 
    by_contra h
    rw [h] at h₁
    norm_num at h₁
  have h₃ : 3 * a = 2 * b := by 
    field_simp [hb] at h₀
    linarith
  have h₄ : 5 * b = 3 * c := by 
    field_simp [hc] at h₁
    linarith
  have ha : a = 2 / 3 * b := by 
    linarith
  have hc' : c = 5 / 3 * b := by 
    linarith
  rw [ha, hc'] at h₂
  have eq1 : 38 / 9 * b^2 = 10 / 9 * b^3 := by
    nlinarith
  have eq2 : 38 * b^2 = 10 * b^3 := by
    have h : (9 : ℚ) ≠ 0 := by norm_num
    field_simp at eq1
    linarith
  have eq3 : 10 * b^3 - 38 * b^2 = 0 := by
    linarith
  have eq4 : b^2 * (10 * b - 38) = 0 := by
    ring_nf at eq3 ⊢
    linarith
  cases (mul_eq_zero.mp eq4) with
  | inl hbl =>
    have hb0 : b = 0 := by
      simp at hbl ⊢
      exact hbl
    contradiction
  | inr hbr =>
    have hb_eq : b = 19 / 5 := by
      linarith
    have ha_eq : a = 38 / 15 := by 
      rw [ha, hb_eq]
      norm_num
    have hc_eq : c = 19 / 3 := by 
      rw [hc', hb_eq]
      norm_num
    rw [ha_eq, hb_eq, hc_eq]
    norm_num