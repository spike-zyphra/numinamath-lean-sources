import Mathlib

open Real
open scoped BigOperators

theorem inequalities_601713
  (x y z : ℝ)
  (h₀ : 0 ≤ x)
  (h₁ : 0 ≤ y)
  (h₂ : 0 ≤ z)
  (h₃ : x * y + y * z + z * x = 1) :
  5 / 2 ≤ 1 / (x + y) + 1 / (y + z) + 1 / (z + x) := by
  have h4 : 0 < x + y := by
    by_contra h
    push_neg at h
    have hx : x = 0 := by
      nlinarith
    have hy : y = 0 := by
      nlinarith
    rw [hx, hy] at h₃
    nlinarith
  have h5 : 0 < y + z := by
    by_contra h
    push_neg at h
    have hy : y = 0 := by
      nlinarith
    have hz : z = 0 := by
      nlinarith
    rw [hy, hz] at h₃
    nlinarith
  have h6 : 0 < z + x := by
    by_contra h
    push_neg at h
    have hz : z = 0 := by
      nlinarith
    have h7 : x = 0 := by
      nlinarith
    rw [hz, h7] at h₃
    nlinarith
  have h7 : 1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2 ≥ 0 := by
    have pos1 : 0 < (x + y) * (y + z) * (z + x) := by
      positivity
    have h8 : (1 / (x + y) + 1 / (y + z) + 1 / (z + x) - 5 / 2) = ( ( (y + z) * (z + x) + (x + y) * (z + x) + (x + y) * (y + z) - 5 / 2 * (x + y) * (y + z) * (z + x) ) / ( (x + y) * (y + z) * (z + x) ) ) := by
      field_simp
      ring
    rw [h8] at *
    apply div_nonneg
    nlinarith [sq_nonneg (x - y), sq_nonneg (y - z), sq_nonneg (z - x),
      sq_nonneg (x + y + z - 2), sq_nonneg (x * y + y * z + z * x - 1),
      h₀, h₁, h₂, mul_nonneg h₀ h₁, mul_nonneg h₁ h₂, mul_nonneg h₂ h₀
    ]
    positivity
  linarith