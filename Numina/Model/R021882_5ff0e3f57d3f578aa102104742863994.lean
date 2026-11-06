import Mathlib

theorem algebra_279805 (x y z : ℝ) (h₀ : 0 < x ∧ 0 < y ∧ 0 < z)
    (h₁ : ∃ r, 4 * y = 3 * x * r ∧ 5 * z = 4 * y * r)
    (h₂ : ∃ d, 1 / y = 1 / x + d ∧ 1 / z = 1 / y + d) :
    x / z + z / x = 34 / 15 := by
  rcases h₀ with ⟨hx, hy, hz⟩
  rcases h₁ with ⟨r, h₁₁, h₁₂⟩
  rcases h₂ with ⟨d, h₂₁, h₂₂⟩
  have hx1 : x ≠ 0 := by linarith
  have hy1 : y ≠ 0 := by linarith
  have hz1 : z ≠ 0 := by linarith
  have h₃ : 16 * y ^ 2 = 15 * x * z := by
    have eq1 : r = (4 * y) / (3 * x) := by
      have hx2 : 3 * x ≠ 0 := by nlinarith
      field_simp
      nlinarith
    rw [eq1] at h₁₂
    have hx2 : 3 * x ≠ 0 := by nlinarith
    field_simp at h₁₂ ⊢
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  have h₄ : 2 * x * z = y * (x + z) := by
    have h5 : 1 / z = 1 / x + 2 * d := by 
      have eq1 : 1 / y = 1 / x + d := h₂₁
      have eq2 : 1 / z = 1 / y + d := h₂₂
      nlinarith [eq1, eq2]
    have h8 : d = (1 / z - 1 / x) / 2 := by 
      linarith [h5]
    rw [h8] at h₂₁
    field_simp [show x ≠ 0 by linarith, show y ≠ 0 by linarith, 
      show z ≠ 0 by linarith] at h₂₁ h5 ⊢
    nlinarith [mul_pos hx hy, mul_pos hx hz, mul_pos hy hz]
  -- Simplify expression
  have h₆ : x / z + z / x = 34 / 15 := by
    have hx1 : x ≠ 0 := by linarith
    have hz1 : z ≠ 0 := by linarith
    have h7 : x / z + z / x = (x ^ 2 + z ^ 2) / (x * z) := by
      field_simp [show z ≠ 0 by linarith, show x ≠ 0 by linarith]
      <;> ring
    rw [h7]
    have h8 : x ^ 2 + z ^ 2 = (x + z) ^ 2 - 2 * (x * z) := by
      nlinarith
    have h9 : (x + z) = (2 * (x * z)) / y := by
      have h10 : 2 * x * z = y * (x + z) := h₄
      have hy1 : y ≠ 0 := by linarith
      field_simp at h10 ⊢
      <;> nlinarith
    have hxz : x * z = (16 / 15) * y ^ 2 := by
      nlinarith [h₃]
    rw [h8, h9, hxz]
    field_simp [show y ≠ 0 by linarith, show x ≠ 0 by linarith, show z ≠ 0 by linarith]
    <;> nlinarith [sq_pos_of_pos hx, sq_pos_of_pos hy, sq_pos_of_pos hz, h₃]
  linarith [h₆]