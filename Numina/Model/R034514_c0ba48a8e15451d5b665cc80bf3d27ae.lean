import Mathlib

theorem algebra_263492 (p q r s : ℝ)
    (h₀ : p^2 + q^2 + r^2 + s^2 = 4) (h₁ : p * q + r * s = 1) :
    (|p - q| ≤ 1 ∨ |p - r| ≤ 1 ∨ |p - s| ≤ 1 ∨ |q - r| ≤ 1 ∨ |q - s| ≤ 1 ∨ |r - s| ≤ 1) ∧
    (|p - q| ≥ 1 ∨ |p - r| ≥ 1 ∨ |p - s| ≥ 1 ∨ |q - r| ≥ 1 ∨ |q - s| ≥ 1 ∨ |r - s| ≥ 1) := by
  have h2 : (p - q) ^ 2 + (r - s) ^ 2 = 2 := by
    nlinarith [sq_nonneg (p + q - (r + s)), sq_nonneg (p + q + (r + s)), h₀, h₁]
  constructor
  · -- Prove that some two of these four numbers differ by at most 1
    by_contra h
    push_neg at h
    have h4 : |p - q| > 1 := h.1
    have h7 : |r - s| > 1 := by
      tauto
    have h6 : (p - q) ^ 2 > 1 := by
      cases' abs_cases (p - q) with h11 h11
      · -- |p - q| > 1
        nlinarith
      · -- |p - q| > 1
        nlinarith
    have h77 : (r - s) ^ 2 > 1 := by
      cases' abs_cases (r - s) with h11 h11
      · -- |r - s| > 1
        nlinarith
      · -- |r - s| > 1
        nlinarith
    nlinarith
  · -- Prove that some 2 differ by at least 1
    by_contra h
    push_neg at h
    have h4 : |p - q| < 1 := by
      linarith [h.1]
    have h7 : |p - r| < 1 := by
      linarith [h.2.1]
    have h12 : |p - s| < 1 := by
      linarith [h.2.2.1]
    have h13 : |q - r| < 1 := by
      linarith [h.2.2.2.1]
    have h14 : |q - s| < 1 := by
      linarith [h.2.2.2.2.1]
    have h15 : |r - s| < 1 := by
      linarith [h.2.2.2.2.2]
    have h88 : (p - q) ^ 2 < 1 := by
      cases' abs_cases (p - q) with h88 h88
      · -- |p - q| < 1
        nlinarith
      · -- |p - q| < 1
        nlinarith
    have h89 : (r - s) ^ 2 < 1 := by
      cases' abs_cases (r - s) with h89 h89
      · -- |r - s| < 1
        nlinarith
      · -- |r - s| < 1
        nlinarith
    nlinarith