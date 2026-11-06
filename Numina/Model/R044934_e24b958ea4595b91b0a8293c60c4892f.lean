import Mathlib

theorem algebra_187271 {x y : ℝ} (h₀ : 0 ≤ x - y) (h₁ : 0 ≤ x + y)
    (h₂ : x - y ≠ 4) (h₃ : 3 * (2 - Real.sqrt (x - y))⁻¹ + 10 * (2 + Real.sqrt (x + y))⁻¹ = 5)
    (h₄ : 4 * (2 - Real.sqrt (x - y))⁻¹ - 5 * (2 + Real.sqrt (x + y))⁻¹ = 3) :
    x = 5 ∧ y = 4 := by

  have h5 : (2 - Real.sqrt (x - y)) ≠ 0 := by
    by_contra h
    have h6 : x - y = 4 := by
      nlinarith [Real.sqrt_nonneg (x - y), Real.sq_sqrt (show (0 : ℝ) ≤ x - y by linarith)]
    contradiction

  have h6 : (2 + Real.sqrt (x + y)) ≠ 0 := by
    by_contra h
    have h7 : Real.sqrt (x + y) = -2 := by linarith
    have h8 : 0 ≤ Real.sqrt (x + y) := Real.sqrt_nonneg (x + y)
    nlinarith

  have eq3 : (2 - Real.sqrt (x - y))⁻¹ = 1 := by
    have eq4 : 3 * (2 - Real.sqrt (x - y))⁻¹ + 10 * (2 + Real.sqrt (x + y))⁻¹ = 5 := h₃
    have eq5 : 4 * (2 - Real.sqrt (x - y))⁻¹ - 5 * (2 + Real.sqrt (x + y))⁻¹ = 3 := h₄
    field_simp [h5, h6] at eq4 eq5 ⊢
    nlinarith [Real.sqrt_nonneg (x - y), Real.sqrt_nonneg (x + y), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x - y by linarith), 
      Real.sq_sqrt (show (0 : ℝ) ≤ x + y by linarith)
    ]

  have eq7 : 2 - Real.sqrt (x - y) = 1 := by
    field_simp [h5] at eq3 ⊢
    all_goals linarith

  have h7 : Real.sqrt (x - y) = 1 := by
    nlinarith

  have h8 : x - y = 1 := by
    have h7' : Real.sqrt (x - y) = 1 := h7
    rw [Real.sqrt_eq_iff_sq_eq] at h7'
    · linarith
    all_goals nlinarith

  have eq4 : (2 + Real.sqrt (x + y))⁻¹ = 1 / 5 := by
    have eq3' : 3 * (2 - Real.sqrt (x - y))⁻¹ + 10 * (2 + Real.sqrt (x + y))⁻¹ = 5 := h₃
    rw [eq3] at eq3'
    field_simp at eq3' ⊢
    all_goals nlinarith [h5, h6, Real.sqrt_nonneg (x - y), Real.sqrt_nonneg (x + y), Real.sq_sqrt (show (0 : ℝ) ≤ x - y by linarith), Real.sq_sqrt (show (0 : ℝ) ≤ x + y by linarith)]

  have eq8 : 2 + Real.sqrt (x + y) = 5 := by
    field_simp [h6] at eq4 ⊢
    all_goals nlinarith

  have h9 : Real.sqrt (x + y) = 3 := by
    nlinarith

  have h10 : x + y = 9 := by
    have h9' : Real.sqrt (x + y) = 3 := h9
    rw [Real.sqrt_eq_iff_sq_eq] at h9'
    · linarith
    all_goals nlinarith

  have hx : x = 5 := by
    linarith [h8, h10]

  have hy : y = 4 := by
    linarith [h8, h10, hx]

  exact ⟨hx, hy⟩