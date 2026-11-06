import Mathlib

theorem algebra_10509 {x y z : ℝ} (h₀ : 0 < x) (h₁ : 0 < y) (h₂ : 0 < z)
    (h₃ : ∃ r, 4 * y = 3 * x * r ∧ 5 * z = 4 * y * r)
    (h₄ : ∃ d, 1 / y = 1 / x + d ∧ 1 / z = 1 / y + d) :
    x / z + z / x = 34 / 15 := by

  rcases h₃ with ⟨r, h₅, h₆⟩
  rcases h₄ with ⟨d, h₇, h₈⟩

  have eq1 : 16 * y ^ 2 = 15 * (x * z) := by
    have eq2 : (4 * y) * (4 * y) = (3 * x) * (5 * z) := by
      have eq3 : 4 * y = 3 * x * r := h₅
      have eq4 : 5 * z = 4 * y * r := h₆
      have h₈ : r = (4 * y) / (3 * x) := by
        have : x ≠ 0 := by linarith
        field_simp
        nlinarith [eq3]
      rw [h₈] at eq4
      have : x ≠ 0 := by linarith
      have : 3 * x ≠ 0 := by
        nlinarith
      have eq5 : 5 * z * (3 * x) = 4 * y * (4 * y) := by
        have h₉ : x ≠ 0 := by linarith
        have h₁₀ : 3 * x ≠ 0 := by
          nlinarith
        have eq7 : 5 * z = 4 * y * ((4 * y) / (3 * x)) := by linarith [eq4]
        field_simp [h₉] at eq7 ⊢
        nlinarith [eq7]
      nlinarith
    nlinarith

  have eq3 : x * y + y * z = 2 * (x * z) := by
    field_simp [show y ≠ 0 by linarith, show x ≠ 0 by linarith, show z ≠ 0 by linarith] at h₇ h₈ ⊢
    nlinarith [h₇, h₈, mul_pos h₀ h₁, mul_pos h₁ h₂, mul_pos h₀ h₂]

  have eq4 : (x + z) ^ 2 = (64 / 15) * (x * z) := by
    have eq5 : y ≠ 0 := by linarith
    have eq6 : x + z ≠ 0 := by nlinarith
    have eq7 : y = (2 * (x * z)) / (x + z) := by
      have h₂ : x + z ≠ 0 := by nlinarith
      field_simp
      nlinarith [eq3]
    rw [eq7] at eq1
    have : x + z ≠ 0 := by nlinarith
    field_simp [(show x + z ≠ 0 by nlinarith), (show x ≠ 0 by linarith), (show z ≠ 0 by linarith)] at eq1 ⊢
    nlinarith [eq1, sq_pos_of_pos h₀, sq_pos_of_pos h₂, mul_pos h₀ h₂]

  have h3 : x / z + z / x = (x ^ 2 + z ^ 2) / (x * z) := by
    field_simp [(show z ≠ 0 by linarith), (show x ≠ 0 by linarith)]
    <;> ring

  rw [h3]

  have eq9 : x ^ 2 + z ^ 2 = (x + z) ^ 2 - 2 * (x * z) := by
    linarith

  rw [eq9]
  rw [eq4]
  field_simp [(show x * z ≠ 0 by
    have hx : x ≠ 0 := by linarith
    have hz : z ≠ 0 := by linarith
    simp [hx, hz]
    all_goals nlinarith
  ), sq_pos_of_pos h₀, sq_pos_of_pos h₂, mul_pos h₀ h₂]
  <;> nlinarith [sq_pos_of_pos h₀, sq_pos_of_pos h₂, mul_pos h₀ h₂, eq4]