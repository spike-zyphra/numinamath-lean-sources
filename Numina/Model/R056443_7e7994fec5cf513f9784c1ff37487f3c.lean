import Mathlib

theorem algebra_306905 (a : ℝ) (x₁ x₂ : ℝ) (h : x₁^2 + a * x₁ + a = 2) (h' : x₂^2 + a * x₂ + a = 2)
    (h'' : x₁ ≠ x₂) :
    (x₁ - 2 * x₂) * (x₂ - 2 * x₁) ≤ -63 / 8 := by
  have h1 : x₁ ^ 2 + a * x₁ + a - 2 = 0 := by linarith
  have h2 : x₂ ^ 2 + a * x₂ + a - 2 = 0 := by linarith
  have h5 : (x₁ - x₂) * (x₁ + x₂ + a) = 0 := by
    nlinarith
  cases (mul_eq_zero.mp h5) with
  | inl h6 =>
    exfalso
    apply h''
    linarith
  | inr h7 =>
    have h8 : x₁ + x₂ = -a := by linarith
    have h8' : x₁ * x₂ = a - 2 := by
      have hsum : x₁ + x₂ = -a := h8
      nlinarith [sq_pos_of_ne_zero (sub_ne_zero.mpr h''), sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - a)]
      <;> nlinarith [sq_nonneg (x₁ - x₂), sq_nonneg (x₁ + x₂ - a)]
      <;> nlinarith [sq_nonneg (x₁ * x₂), sq_nonneg (x₁ + x₂)]
    have h9 : (x₁ - 2 * x₂) * (x₂ - 2 * x₁) = 5 * (x₁ * x₂) - 2 * ((x₁ ^ 2 + x₂ ^ 2)) := by
      nlinarith [sq_nonneg (x₁ - x₂), h8]
    have h9' : x₁ ^ 2 + x₂ ^ 2 = (x₁ + x₂) ^ 2 - 2 * (x₁ * x₂) := by
      nlinarith
    have h9'' : x₁ ^ 2 + x₂ ^ 2 = a^2 - 2 * a + 4 := by
      rw [h8, h8'] at h9'
      nlinarith
    nlinarith [sq_nonneg (a - 9 / 4), h9, h9'', h8']
    <;> nlinarith [sq_nonneg (a - 9 / 4)]