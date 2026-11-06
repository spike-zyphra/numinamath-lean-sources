import Mathlib

theorem algebra_135327 {a : ℝ} (ha : a ≠ -1) (x₁ x₂ : ℝ)
    (h₁ : (2 * a + 2) * x₁^2 + (2 * a + 3) * x₁ + 1 = 0) (h₂ : (2 * a + 2) * x₂^2 + (2 * a + 3) * x₂ + 1 = 0)
    (h₃ : x₁ / x₂ = 1 / 3) :
    a = 1 / 2 ∨ a = -5 / 6 := by

  have h₄ : x₂ ≠ 0 := by
    by_contra h
    rw [h] at h₃
    norm_num at h₃

  have h₅ : 3 * x₁ = x₂ := by
    field_simp [h₄] at h₃
    linarith

  have h₆ : x₂ = 3 * x₁ := by linarith [h₅]
  rw [h₆] at h₂

  have eq1 :9 * (2 * a + 2) * x₁ ^ 2 + 3 * (2 * a + 3) * x₁ + 1 = 0 := by 
    nlinarith

  have eq2 : (2 * a + 2) * x₁ ^ 2 + (2 * a + 3) * x₁ + 1 = 0 := h₁

  have eq3 : (2 * a + 3) * x₁ = -4 / 3 := by
    nlinarith

  have eq4 : (2 * a + 2) * x₁ ^ 2 = 1 / 3 := by
    nlinarith

  have hx1 : x₁ ≠ 0 := by
    intro h_zero
    have h_zero : x₁ = 0 := by linarith
    rw [h_zero] at eq3 eq4
    nlinarith

  by_cases h9 : (2 * a + 3) = 0
  · -- Case 2a+3 = 0
    have h10 : a = -3/2 := by linarith
    rw [h10] at eq3 eq4
    nlinarith
  · -- Case 2a+3 ≠ 0
    have eq6 : x₁ = ( -4/3 ) / (2 * a + 3) := by 
      field_simp [h9] at *
      nlinarith

    have eq7 : x₁ ^ 2 = ( -4/3 / (2 * a + 3) ) ^ 2 := by 
      rw [eq6]
    have eq8 : (2 * a + 2) * ( (-4/3 / (2 * a + 3)) ^ 2 ) = 1/3 := by 
      rw [eq7] at eq4 
      linarith

    have eq9 : (2 * a + 2) * 16/(9*(2*a+3)^2) = 1/3 := by 
      have eq9' : ((2 * a + 2) * ((-4/3 / (2 * a + 3)) ^ 2 ) ) = 1/3 := by 
        linarith
      have eq10' : ((2 * a + 2) * ((-4/3 / (2 * a + 3)) ^ 2 )) = (2 * a + 2) * 16/(9 * (2 * a + 3) ^ 2) := by 
        field_simp [h9] at *
        <;> nlinarith
      nlinarith

    have eq10 : (2 * a + 2) * 16 = 3 * (2 * a + 3) ^ 2 := by 
      field_simp [h9] at eq9
      nlinarith

    have eq11 : 12 * a ^ 2 + 4 * a - 5 = 0 := by 
      nlinarith
    have h9 : (a - 1 / 2) * (a + 5 / 6) = 0 := by 
      nlinarith
    cases' mul_eq_zero.mp h9 with h10 h11
    · left
      linarith
    · right
      linarith