import Mathlib

theorem number_theory_3265
    (a : ℤ)
    (h : a^3 = 10503459) :
    a = 219 := by 
  have h1 : a^3 = 10503459 := h
  have h2 : a ≤ 219 := by
    by_contra h2
    push_neg at h2
    have h3 : a ≥ 220 := by 
      omega
    have h4 : a^3 ≥ 220^3 := by
      have h5 : a ≥ 220 := h3
      have h6 : a^3 ≥ 220^3 := by
        have h11 : a ≥ 220 := h5
        have h12 : (a : ℤ) ≥ (220 : ℤ) := h11
        have h13 : a^3 ≥ (220 : ℤ) ^3 := by
          nlinarith [sq_nonneg (a - 220 : ℤ), sq_nonneg ((a + 220 : ℤ)), sq_nonneg ((a) - 220), sq_nonneg ((a) + 220), sq_nonneg (a^2 - (220 : ℤ)^2), sq_nonneg ((a : ℤ) * (220 : ℤ))]
        linarith
      linarith
    nlinarith
  have h3 : a ≥ 219 := by
    by_contra h4
    push_neg at h4
    have h4 : a ≤ 218 := by 
      omega
    have h5 : a^3 ≤ 218^3 := by
      have h6 : a ≤ 218 := h4
      have h7 : a^3 ≤ 218^3 := by
        have h11 : a ≤ 218 := h6
        have h12 : (a : ℤ) ≤ (218 : ℤ) := h11
        have h13 : a^3 ≤ (218 : ℤ) ^3 := by
          nlinarith [sq_nonneg (a - 218 : ℤ), sq_nonneg ((a + 218 : ℤ)), sq_nonneg ((a) - 218), sq_nonneg ((a) + 218), sq_nonneg (a^2 - (218 : ℤ)^2), sq_nonneg ((a : ℤ) * (218 : ℤ))]
        linarith
      linarith
    nlinarith
  have h4 : a = 219 := by 
    linarith
  exact h4