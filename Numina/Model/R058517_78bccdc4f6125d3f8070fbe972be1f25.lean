import Mathlib

theorem algebra_871 {a b c x y z : ℝ} (h : a ≠ 0 ∧ b ≠ 0 ∧ c ≠ 0 ∧ x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0)
    (h₀ : a * x = 1 ∧ b * y = 1 ∧ c * z = 1) :
    1 / (1 + a ^ 4) + 1 / (1 + b ^ 4) + 1 / (1 + c ^ 4) +
    1 / (1 + x ^ 4) + 1 / (1 + y ^ 4) + 1 / (1 + z ^ 4) = 3 := by
  rcases h with ⟨ha, hb, hc, hx, hy, hz⟩
  rcases h₀ with ⟨h₀₁, h₀₂, h₀₃⟩
  have hx_eq : x = 1 / a := by
    field_simp [ha]
    <;> nlinarith
  have hy_eq : y = 1 / b := by
    field_simp [hb]
    <;> nlinarith
  have hz_eq : z = 1 / c := by
    field_simp [hc]
    <;> nlinarith
  rw [hx_eq, hy_eq, hz_eq]
  have h₁ : 1 / (1 + a ^ 4) + 1 / (1 + (1 / a) ^ 4) = 1 := by
    have h₁₀ : 1 / (1 + (1 / a) ^ 4) = a ^ 4 / (1 + a ^ 4) := by
      field_simp [ha]
      <;> ring
    rw [h₁₀]
    field_simp [ha]
    <;> ring
  have h₂ : 1 / (1 + b ^ 4) + 1 / (1 + (1 / b) ^ 4) = 1 := by
    have h₂₀ : 1 / (1 + (1 / b) ^ 4) = b ^ 4 / (1 + b ^ 4) := by
      field_simp [hb]
      <;> ring
    rw [h₂₀]
    field_simp [hb]
    <;> ring
  have h₃ : 1 / (1 + c ^ 4) + 1 / (1 + (1 / c) ^ 4) = 1 := by
    have h₃₀ : 1 / (1 + (1 / c) ^ 4) = c ^ 4 / (1 + c ^ 4) := by
      field_simp [hc]
      <;> ring
    rw [h₃₀]
    field_simp [hc]
    <;> ring
  linarith [h₁, h₂, h₃]