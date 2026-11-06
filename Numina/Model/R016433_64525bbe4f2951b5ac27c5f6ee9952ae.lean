import Mathlib

theorem algebra_251403 {a b c x y z : ℝ} (h₀ : a * b * c ≠ 0) (h₁ : x * y * z ≠ 0)
    (h₂ : x / a + y / b + z / c = 1) (h₃ : a / x + b / y + c / z = 0) :
    x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 1 := by
  have h₄ : a ≠ 0 := by
    by_contra h
    have h₅ : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have h₅ : b ≠ 0 := by
    by_contra h
    have h₆ : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have h₆ : c ≠ 0 := by
    by_contra h
    have h₇ : a * b * c = 0 := by
      rw [h]
      norm_num
    contradiction
  have hx : x ≠ 0 := by
    by_contra h
    have h₇ : x * y * z = 0 := by
      rw [h]
      norm_num
    contradiction
  have hy : y ≠ 0 := by
    by_contra h
    have h₈ : x * y * z = 0 := by
      rw [h]
      norm_num
    contradiction
  have hz : z ≠ 0 := by
    by_contra h
    have h₉ : x * y * z = 0 := by
      rw [h]
      norm_num
    contradiction

  have eq1 : x * (b * c) + y * (a * c) + z * (a * b) = a * b * c := by 
    have eq1 : x / a + y / b + z / c = 1 := h₂
    field_simp [h₄, h₅, h₆] at eq1 ⊢
    linarith
  have eq2 : a * (y * z) + b * (x * z) + c * (x * y) = 0 := by
    have eq2 : a / x + b / y + c / z = 0 := h₃
    field_simp [hx, hy, hz] at eq2 ⊢
    nlinarith

  have eq3 : x ^ 2 / a ^ 2 + y ^ 2 / b ^ 2 + z ^ 2 / c ^ 2 = 1 := by
    have eq4 : (x / a + y / b + z / c) ^ 2 = 1 := by
      rw [h₂]
      norm_num
    have eq5 : (x / a + y / b + z / c) ^ 2 = x^2 / a^2 + y^2 / b^2 + z^2 / c^2 + 2 * (x * y / (a * b) + x * z / (a * c) + y * z / (b * c)) := by 
      field_simp [h₄, h₅, h₆]
      ring
    have h4 : x * y / (a * b) + x * z / (a * c) + y * z / (b * c) = 0 := by 
      have eq6 : (a * y * z + b * x * z + c * x * y) = 0 := by
        linarith [eq2]
      have h7 : x * y / (a * b) + x * z / (a * c) + y * z / (b * c) = (a * y * z + b * x * z + c * x * y) / (a * b * c) := by
        field_simp [h₄, h₅, h₆]
        ring
      rw [h7]
      field_simp [show a * b * c ≠ 0 by assumption]
      <;> nlinarith
    nlinarith [eq4, eq5, h4]
  exact_mod_cast eq3