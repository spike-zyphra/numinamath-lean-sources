import Mathlib

theorem algebra_3551 {x y : ℝ} (hx : x ≠ y) (h₁ : x^2 + Real.sqrt 3 * y = 4) (h₂ : y^2 + Real.sqrt 3 * x = 4) :
x / y + y / x = -5 := by
  have h3 : x ≠ y := hx
  have h4 : x^2 - y^2 + Real.sqrt 3 * (y - x) = 0 := by
    linarith
  
  have eq1 : (x - y) * (x + y - Real.sqrt 3) = 0 := by 
    have eq1 : x^2 - y^2 + Real.sqrt 3 * (y - x) = 0 := h4
    have eq2 : x^2 - y^2 = (x - y) * (x + y) := by ring
    rw [eq2] at eq1
    have eq3 : Real.sqrt 3 * (y - x) = - Real.sqrt 3 * (x - y) := by ring
    rw [eq3] at eq1 
    ring_nf at eq1 ⊢
    linarith
  
  have eq2 : x + y = Real.sqrt 3 := by 
    cases' (mul_eq_zero.mp eq1) with eq3 eq4 
    · -- `eq3 : x - y = 0` contradicts `hx : x ≠ y`.
      exfalso
      apply hx
      linarith
    · -- From `eq4 : x + y - Real.sqrt 3 = 0`.
      nlinarith
  
  have eq3 : x^2 + y^2 = 5 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 from by norm_num), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h_eq
      apply hx
      linarith
    ), sq_nonneg (x - y), h₁, h₂, eq2]

  have eq4 : x * y = -1 := by
    nlinarith [Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 from by norm_num), sq_pos_of_ne_zero (show (x - y : ℝ) ≠ 0 by
      intro h_eq
      apply hx
      linarith
    ), sq_nonneg (x - y), h₁, h₂, eq2, eq3]

  have h5 : y ≠ 0 := by
    by_contra h_eq
    have eq5 : y = 0 := by linarith [h_eq]
    rw [eq5] at h₁ h₂ eq4
    nlinarith [sq_nonneg x, sq_nonneg y, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 from by norm_num)]

  have h6 : x ≠ 0 := by
    by_contra h_eq
    have eq6 : x = 0 := by linarith [h_eq]
    rw [eq6] at h₁ h₂ eq4
    nlinarith [sq_nonneg x, sq_nonneg y, Real.sqrt_nonneg 3, Real.sq_sqrt (show 0 ≤ 3 from by norm_num)]
  
  have eq7 : x / y + y / x = (x^2 + y^2) / (x * y) := by
    field_simp [h5, h6]
    <;> ring
  
  have eq8 : (x^2 + y^2) / (x * y) = -5 := by
    have eq9 : x * y = -1 := eq4
    have eq10 : x^2 + y^2 = 5 := eq3
    field_simp [h5, h6, eq9]
    <;> nlinarith

  linarith [eq7, eq8]