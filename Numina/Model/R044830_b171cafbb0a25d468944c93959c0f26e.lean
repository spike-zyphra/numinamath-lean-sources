import Mathlib

theorem algebra_273736 {a b c : ℤ} (h₀ : a ≠ b) (h₁ : a ≠ c) (h₂ : b ≠ c)
    (h₃ : a * b * c = 17955) (h₄ : ∃ d, b = a + d ∧ c = b + d)
    (h₅ : ∃ r, (3 * a + b) * r = 3 * b + c ∧ (3 * b + c) * r = 3 * c + a) :
    a + b + c = -63 := by
  rcases h₄ with ⟨d, h₄₁, h₄₂⟩
  rcases h₅ with ⟨r, h₅₁, h₅₂⟩
  have h₆ : c = 2 * b - a := by
    nlinarith
  have h₇ : b = a + d := by linarith
  have h₈ : c = a + 2 * d := by
    nlinarith
  rw [show b = a + d by linarith, show c = a + 2 * d by nlinarith] at h₃
  have h₉ : (4 * a + d) * r = 4 * a + 5 * d := by
    have h₁₀ : (3 * a + b) * r = 3 * b + c := h₅₁
    rw [show b = a + d by linarith, show c = a + 2 * d by nlinarith] at h₁₀
    linarith
  have h₁₀ : (4 * a + 5 * d) * r = 4 * a + 6 * d := by
    have h₁₁ : (3 * b + c) * r = 3 * c + a := h₅₂
    rw [show b = a + d by linarith, show c = a + 2 * d by nlinarith] at h₁₁
    linarith
  have h₁₁ : d * (4 * r - 1) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h₁₁) with
  | inl h₁₂ =>
    have h₁₃ : d = 0 := by linarith
    rw [show d = 0 by linarith] at h₃ h₉ h₁₀
    -- Now, h₃ is a^3 = 17955
    have h14 : a^3 = 17955 := by
      nlinarith
    -- This is a contradiction because 17955 is not a perfect cube
    have h15 : a ≤ 26 := by
      nlinarith [sq_nonneg (a - 26 : ℤ), sq_nonneg (a^2 - 26*a : ℤ), sq_nonneg (a - 27 : ℤ), sq_nonneg (a + 27 : ℤ)]
    have h18 : a ≥ 26 := by
      nlinarith [sq_nonneg (a - 26 : ℤ), sq_nonneg (a^2 - 26*a : ℤ), sq_nonneg (a - 27 : ℤ), sq_nonneg (a + 27 : ℤ)]
    have h19 : a = 26 := by
      linarith
    rw [h19] at h14
    norm_num at h14
  | inr h₁₄ =>
    have h15 : 4 * r = 1 := by
      linarith
    omega