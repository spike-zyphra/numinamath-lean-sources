import Mathlib

theorem algebra_13304 (a b c : ℝ) (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
    (h₁ : a * b * c = 216) (h₂ : 2 * (a * b + b * c + c * a) = 288)
    (h₃ : ∃ r, b = a * r ∧ c = b * r) :
    4 * (a + b + c) = 96 := by 
  rcases h₃ with ⟨r, hab, hac⟩
  have hb : b = a * r := hab
  have hc : c = a * r^2 := by
    have h1 : c = b * r := hac
    rw [h1]
    rw [hb]
    all_goals nlinarith
  rw [hb] at h₁ h₂
  rw [hc] at h₁ h₂
  have h4 : a ^ 3 * r^ 3 = 216 := by
    nlinarith
  have h6 : a * r = 6 := by
    have h7 : a ^ 3 * r^ 3 = 216 := h4
    have h8 : (a * r) ^ 3 = 216 := by
      nlinarith
    have h9 : a * r > 0 := by
      nlinarith [h₀.1, h₀.2.1, h₀.2.2]
    have h10 : a * r = 6 := by
      have h11 : (a * r) ^ 3 - 216 = 0 := by nlinarith
      have h12 : (a * r - 6) * ((a * r)^2 + (a * r) * 6 + 36) = 0 := by 
        ring_nf at h11 ⊢
        nlinarith
      cases' (mul_eq_zero.mp h12) with h13 h14
      · -- Case where `a * r - 6 = 0`.
        linarith
      · -- Case where `(a * r) ^ 2 + (a * r) * 6 + 36 = 0`.
        nlinarith [sq_nonneg ((a * r) + 3), h₀.1]
    linarith
  nlinarith [sq_nonneg (a * r), sq_nonneg (a * (a * r * r)), sq_nonneg (a * r - 6), sq_nonneg ((a - 6 / a)), h₀.1, h₀.2.1, h₀.2.2, h6]